(defpackage :dump
  (:use :common-lisp)
  (:import-from :alexandria :iota :once-only :with-gensyms)
  (:import-from :ironclad :with-octet-input-stream :with-octet-output-stream)
  (:import-from :listopia :all :any :split-at)
  (:import-from :str
   :concat :contains? :join :s-rest :split :starts-with?
   :trim-right :words)
  (:import-from :trivia :lambda-match :match)
  (:import-from :trivial-utf-8 :string-to-utf-8-bytes)
  (:export
   :db-matrix-column-ref
   :main
   :with-data-db))

(in-package :dump)


;; Utilities
(defun for-each-indexed (function list &optional (start 0))
  "Apply FUNCTION successively on every element of LIST.  FUNCTION is
invoked as (FUNCTION INDEX ELEMENT) where ELEMENT is an element of
LIST and INDEX is its index.  START is the index to use for the first
element."
  (match list
    ((list* head tail)
     (funcall function start head)
     (for-each-indexed function tail (1+ start)))))

(defun assoc-ref (alist key &key (test #'equalp))
  "Given an association list ALIST, return the value associated with
KEY."
  (match (assoc key alist :test test)
    ((cons _ value) value)))

(defmacro save-excursion (stream &body body)
  "Evaluate BODY, and restore STREAM to the position it was in before
evaluation of BODY."
  (with-gensyms (position)
    (once-only (stream)
      `(let* ((,position (file-position ,stream)))
         (unwind-protect
              (progn ,@body)
           (file-position ,stream ,position))))))

(defun unget-line (line stream)
  "Unget LINE to STREAM."
  (file-position stream (- (file-position stream)
                           (1+ (length line)))))

(defun count-lines (stream)
  "Return the number of lines in STREAM starting from the current
position."
  (labels ((count-lines-loop (result)
             (if (read-line stream nil)
                 (count-lines-loop (1+ result))
                 result)))
    (save-excursion stream
      (count-lines-loop 0))))

(defun repeat (thunk n)
  "Run THUNK N times and return the result as a list."
  (labels ((repeat-tail (thunk n result)
             (if (zerop n)
                 result
                 (repeat-tail thunk
                              (1- n)
                              (cons (funcall thunk)
                                    result)))))
    (reverse (repeat-tail thunk n (list)))))

(defun repeat-indexed (function n)
  "Run FUNCTION N times and return the result as a list. FUNCTION is
invoked as (FUNCTION INDEX) for INDEX = 0, 1, 2, ..., n-1."
  (labels ((repeat-tail (function i n result)
             (if (= i n)
                 result
                 (repeat-tail function (1+ i) n (cons (funcall function i)
                                                      result)))))
    (reverse (repeat-tail function 0 n (list)))))

(defun find-index (function n)
  "Return the index between 0 and n-1 (both inclusive) for which
FUNCTION returns non-nil. If no such index exists, return
nil. FUNCTION is invoked as (FUNCTION INDEX). The order of invocation
of FUNCTION is unspecified."
  (unless (zerop n)
    (if (funcall function (1- n))
        (1- n)
        (find-index function (1- n)))))

(defun list-dimensions (list depth)
  "Return the array dimensions of a LIST given the LIST's DEPTH."
  (loop repeat depth
        collect (length list)
        do (setf list (car list))))

(defun list-to-array (list depth)
  "Convert a LIST into an ARRAY given the lists DEPTH."
  (make-array (list-dimensions list depth)
              :initial-contents list))

(defun metadata-key (hash key)
  "Return the database key to retrieve metadata KEY associated with
blob of HASH."
  (concatenate '(vector (unsigned-byte 8))
               hash
               (string-to-utf-8-bytes (concat ":" key))))

(defun write-bytevector-with-length (bv stream)
  "Write length of BV followed by BV itself to STREAM. The length is
written as a little endian 64-bit unsigned integer."
  (write-sequence (lmdb:uint64-to-octets (length bv)) stream)
  (write-sequence bv stream))

(defun bv-hash (bv &optional metadata)
  "Return hash of BV + METADATA. METADATA is an association list mapping
string keys to string, uint64 or bytevector values."
  (ironclad:with-digesting-stream (stream *blob-hash-digest*)
    ;; Write bytevector.
    (write-bytevector-with-length bv stream)
    ;; Write metadata.
    (mapc (lambda-match
            ((cons key value)
             (write-bytevector-with-length (string-to-utf-8-bytes key)
                                           stream)
             (write-bytevector-with-length
              (etypecase value
                (string (string-to-utf-8-bytes value))
                ((unsigned-byte 64) (lmdb:uint64-to-octets value))
                ((vector (unsigned-byte 8)) value))
              stream)))
          metadata)))

(defun hash-vector-length (hash-vector)
  "Return the number of hashes in HASH-VECTOR."
  (/ (length hash-vector)
     (ironclad:digest-length *blob-hash-digest*)))

(defun hash-vector-ref (hash-vector n)
  "Return the Nth hash in HASH-VECTOR."
  (let ((hash-length (ironclad:digest-length *blob-hash-digest*)))
    (make-array hash-length
                :element-type '(unsigned-byte 8)
                :displaced-to hash-vector
                :displaced-index-offset (* n hash-length))))


;; Matrix Structures and Operations
(defvar *blob-hash-digest* :sha256)

(defstruct table matrix metadata)

(defstruct db-table
  db hash nrows ncols row-pointers column-pointers array transpose)

(defun matrix-row (matrix n)
  "Return the Nth row of MATRIX."
  (let ((ncols (array-dimension matrix 1)))
    (make-array ncols
		:element-type (array-element-type matrix)
		:displaced-to matrix
		:displaced-index-offset (* n ncols))))

(defun matrix-column (matrix n)
  "Return the Nth column of MATRIX."
  (let ((column (make-array (array-dimension matrix 0))))
    (dotimes (i (length column))
      (setf (aref column i)
	    (aref matrix i n)))
    column))


;; LMDB Operations

(defmacro with-data-db ((db database-directory &key write) &body body)
  (with-gensyms (env)
    (once-only (database-directory write)
      `(lmdb:with-env (,env ,database-directory
                            :if-does-not-exist :create
                            :map-size (* 100 1024 1024))
         (let ((,db (lmdb:get-db nil :env ,env)))
           (lmdb:with-txn (:env ,env :write ,write)
             ,@body))))))

(defun db-put (db bv &optional metadata)
  "Put BV, a bytevector, into DB. Associate METADATA, an association
list of metadata, with BV. Return the hash."
  (let ((hash (bv-hash bv metadata)))
    ;; Put bytevector and metadata into db. Do nothing if it is
    ;; already in db.
    (unless (db-get db hash)
      (lmdb:put db hash bv)
      (mapc (lambda-match
              ((cons key value)
               (lmdb:put db (metadata-key hash key) value)))
            metadata))
    hash))

(defun db-get (db key)
  "Get bytevector with KEY from DB. KEY may be a hash or a
string. If it is a string, it is encoded into octets before querying
the database."
  (lmdb:g3t db (if (stringp key)
                   (string-to-utf-8-bytes key)
                   key)))

(defun db-metadata-get (db hash key)
  "Get metadata associated with KEY, HASH from DB."
  (db-get db (metadata-key hash key)))

(defun db-current-matrix-hash (db)
  "Return the hash of the current matrix in matrix DB."
  (hash-vector-ref (db-get db "versions") 0))

(defun (setf db-current-matrix-hash) (hash db)
  "Set HASH as the current matrix in matrix DB."
  ;; Prepend hash onto versions array.
  (lmdb:put db (string-to-utf-8-bytes "versions")
            (concatenate '(vector (unsigned-byte 8))
                         hash
                         (db-get db "versions")))
  ;; Write a read-optimized copy of current matrix into the database.
  (let ((matrix (db-matrix db hash)))
    (lmdb:put db
              (string-to-utf-8-bytes "current")
              (db-put
               db
               (with-octet-output-stream (stream)
                 (dotimes (i (db-table-nrows matrix))
                   (write-sequence (db-matrix-row-ref matrix i)
                                   stream))
                 (dotimes (i (db-table-ncols matrix))
                   (write-sequence (db-matrix-column-ref matrix i)
                                   stream)))
               `(("matrix" . ,hash))))))

(defun db-all-matrices (db)
  "Return a list of all matrices in DB, newest first."
  (let ((all-matrix-hashes (db-get db "versions")))
    (mapcar (lambda (i)
              (db-matrix db (hash-vector-ref all-matrix-hashes i)))
            (iota (hash-vector-length all-matrix-hashes)))))

(defun db-matrix (db hash)
  (let ((nrows (lmdb:octets-to-uint64
                (db-metadata-get db hash "nrows")))
        (ncols (lmdb:octets-to-uint64
                (db-metadata-get db hash "ncols")))
        (hash-length (ironclad:digest-length *blob-hash-digest*)))
    (make-db-table
     :db db
     :hash hash
     :nrows nrows
     :ncols ncols
     :row-pointers (make-array (* nrows hash-length)
                               :element-type '(unsigned-byte 8)
                               :displaced-to (db-get db hash))
     :column-pointers (make-array (* ncols hash-length)
                                  :element-type '(unsigned-byte 8)
                                  :displaced-to (db-get db hash)
                                  :displaced-index-offset (* nrows hash-length)))))

(defun db-matrix-put (db data)
  "Put MATRIX into DB and return the hash."
  (let ((matrix (table-matrix data)))
    (match (array-dimensions matrix)
      ((list nrows ncols)
       (db-put
        db
        (with-octet-output-stream (stream)
          (dotimes (i nrows)
            (write-sequence (db-put db (matrix-row matrix i))
                            stream))
          (dotimes (j ncols)
            (write-sequence (db-put db (matrix-column matrix j))
                            stream)))
        `(("nrows" . ,nrows)
          ("ncols" . ,ncols)))))))

(defun db-current-matrix (db)
  "Return the latest version of the matrix in DB."
  (let* ((read-optimized-blob (db-get db (db-get db "current")))
         (current-matrix-hash (db-current-matrix-hash db))
         (nrows (lmdb:octets-to-uint64
                 (db-metadata-get db current-matrix-hash "nrows")))
         (ncols (lmdb:octets-to-uint64
                 (db-metadata-get db current-matrix-hash "ncols"))))
    (make-db-table
     :db db
     :nrows nrows
     :ncols ncols
     :array (make-array (list nrows ncols)
                        :element-type '(unsigned-byte 8)
                        :displaced-to read-optimized-blob)
     :transpose (make-array (list ncols nrows)
                            :element-type '(unsigned-byte 8)
                            :displaced-to read-optimized-blob))))

(defun db-matrix-ref (matrix)
  "Return MATRIX as a 2-dimensional array."
  (let ((array (db-table-array matrix)))
    (if array
        array
        (let* ((nrows (db-table-nrows matrix))
               (ncols (db-table-ncols matrix))
               (array (make-array (list nrows ncols)
                                  :element-type '(unsigned-byte 8))))
          (dotimes (i nrows)
            (let ((row (db-matrix-row-ref matrix i)))
              (dotimes (j ncols)
                (setf (aref array i j)
                      (aref row j)))))
          array))))

(defun db-matrix-row-ref (matrix i)
  "Return the Ith row of db MATRIX."
  (let ((db (db-table-db matrix))
        (array (db-table-array matrix)))
    (if array
        (matrix-row array i)
        (db-get
         db
         (hash-vector-ref (db-table-row-pointers matrix) i)))))

(defun db-matrix-column-ref (matrix j)
  "Return the Jth column of db MATRIX."
  (let ((db (db-table-db matrix))
        (transpose (db-table-transpose matrix)))
    (if transpose
        (matrix-row transpose j)
        (db-get
         db (hash-vector-ref (db-table-column-pointers matrix)
                             j)))))

(defun hash-in-hash-vector-p (hash hash-vector)
  "Return non-nil if HASH is in HASH-VECTOR. Else, return nil."
  (find-index (lambda (i)
                (equalp (hash-vector-ref hash-vector i)
                        hash))
              (hash-vector-length hash-vector)))

(defun live-key-p (db key)
  "Return non-nil if KEY is live. Else, return nil."
  (or (equalp key (string-to-utf-8-bytes "current"))
      (equalp key (string-to-utf-8-bytes "versions"))
      (equalp key (db-get db "current"))
      (let ((versions-hash-vector (db-get db "versions"))
            (key-hash-prefix (make-array (ironclad:digest-length *blob-hash-digest*)
                                         :element-type '(unsigned-byte 8)
                                         :displaced-to key)))
        (or (hash-in-hash-vector-p key-hash-prefix versions-hash-vector)
            (find-index (lambda (i)
                          (hash-in-hash-vector-p
                           key-hash-prefix
                           (db-get db (hash-vector-ref versions-hash-vector i))))
                        (hash-vector-length versions-hash-vector))))))

(defun collect-garbage (db)
  "Delete all keys in DB that are not associated with a live hash."
  (lmdb:with-cursor (cursor db)
    (lmdb:cursor-first cursor)
    (lmdb:do-cursor (key value cursor)
      (unless (live-key-p db key)
        (lmdb:cursor-del cursor)))))



(defun import-into-lmdb (data db-path)
  "Import MATRIX which is a sampledata-matrix object into
DB-PATH."
  (with-data-db (db db-path :write t)
    (let* ((hash (db-matrix-put db data))
	   (db-matrix (db-matrix db hash)))
      ;; Read written data back and verify.
      (unless (and (all (lambda (i)
			  (equalp (matrix-row (table-matrix data) i)
				  (db-matrix-row-ref db-matrix i)))
			(iota (db-table-nrows db-matrix)))
		   (all (lambda (i)
			  (equalp (matrix-column (table-matrix data) i)
				  (db-matrix-column-ref db-matrix i)))
			(iota (db-table-ncols db-matrix))))
	;; Roll back database updates.
	(collect-garbage db)
	;; Exit with error message.
	(format *error-output*
		"Rereading and verifying sampledata matrix written to \"~a\" failed.
This is a bug. Please report it.
"
		db-path)
	(uiop:quit 1))
      ;; Set the current matrix.
      (setf (db-current-matrix-hash db) hash))))
