;;;; RearGuard theorem prover
;;;; Complete rewrite on the top of Modus
;;;; 14.07.2022: v. 1
;;;; 19.02.2023: v. 2
;;;; 8.07.2023: v. 3
;;;; Maxim "BonSavage" Kirillov

(in-package :rearguard)

(defparameter *known* nil)
(defparameter *rules* nil)

;;Reader

(defconstant +read-rules+
  (list

					;(rule
					; (axiom ?x !- ?y)
					; (reduces ?x ?y)) ;Applications successfully deals with it
   
   ;(rule
   ; (axiom ?x !- ?y)
   ; (applicates ?x ?y))

   ;(rule
   ; (axiom ?x <->> ?y)
   ; (reduces ?x ?y))

   ;(rule
   ; (axiom ?x <->> ?y)
   ; (applicates ?y ?x))
   
   (rule (def ?x <=> ?y)
	 (axiom ?x !- ?y))
   
   (rule (def ?x <=> ?y)
	 (axiom ?y !- ?x))

   (rule
    (request ?x -> ?y)
    (applicates ?x ?y))

   (rule
    (request ?x -> ?y)
    (reduces ?x ?y))
   
   (rule
    (reduces ?x ?y)
    (applicates (not ?y) (not ?x)))
   
   (rule
    (applicates ?x ?y)
    (reduces (not ?y) (not ?x)))

   (rule
    (reduces ?z (or ?x ?y))
    (reduces (and ?z (not ?x)) ?y))

   (rule
    (reduces ?z (or ?x ?y))
    (reduces (and ?z (not ?y)) ?x))

   (rule
    (applicates ?z (or ?x ?y))
    (applicates (and ?z (not ?x)) ?y))

   (rule
    (applicates ?z (or ?x ?y))
    (applicates (and ?z (not ?y)) ?y))))

(defun parse-applications(states)
  (let-be [*known* (append states (parse-axioms states))
	   *rules* +read-rules+]
    (variants '(applicates ?x ?y))))

(defun parse-reductions(states)
  (let-be [*known* (append states (parse-axioms states))
	   *rules* +read-rules+]
    (variants '(reduces ?x ?y))))

(defun parse-supply(states)
  (let-be [*known* states
	   *rules* +read-rules+]
    (variants '(supply ?x = ?y))))

(defun reduce-true-once()
  (append (remove-duplicates
	   (mapcar (alexandria:rcurry #'sublis '(false ?x))
		   (evaluate '(newly-false ?x)))
	   :test #'equal)
	  (remove-duplicates
	   (mapcar (alexandria:rcurry #'sublis '(true ?x))
		   (evaluate '(newly-true ?x)))
	   :test #'equal)))

(defun reduce-true(known reductions)
  (let-be [*rules* reductions
	   *known* nil
	   *sweeped* nil]
    (alet ((true known)
	   (newly-true known))
      (let-be [*known* (append newly-true *known*)
	       newly-true (reduce-true-once)
	       true (append newly-true true)]
	(if newly-true
	    (self true newly-true)
	    true)))))

;;;Inference

(defmacro with-axioms ((&rest rules) &body forms)
  `(let ((*known* (append ',rules *known*)))
     ,@forms))

(defstruct environment
  (reductions)
  (applications)
  (supply))

(defmacro define-environment(name &body axioms)
  `(defconstant ,name (make-environment
		       :supply (compile-supply (parse-supply ',axioms))
		       :applications (compile-conclusions (parse-applications ',axioms))
		       :reductions (compile-conclusions (parse-reductions ',axioms)))))

(defmacro with-environment
    (env
     known
     &body forms)
  `(let-be [*rules*  (environment-applications ,env)
	    *known* (reduce-true ,known (environment-reductions ,env))]
	   ,@forms))

(defun infer(stat)
  (let-be [(_ any-true) (evaluate `(true ,stat))
	   (_ any-false) (evaluate `(false ,stat))]
    (cond
      ((and any-true any-false) (error "Contradiction found!"))
      (any-true 'true)
      (any-false 'false)
      (t stat))))

;;Debug

(defun variants(stat)
  (awith (evaluate stat)
    (filtering-map (lambda (sub) (when sub (sublis sub stat))) it)))

(defun print-variants(stat)
  (awith (variants stat)
    (dolist (elem it)
      (format t "~a ~&" elem))))

;;Experimental

(defun parse-axiom(axi)
  (let-be [(list _ prereq _ conseq) axi]
    (list
     (when (<= (length (modus::extract-variables prereq))
	       (length (modus::extract-variables conseq)))
       (list 'applicates prereq conseq))
     (when (>= (length (modus::extract-variables prereq))
	       (length (modus::extract-variables conseq)))
       (list 'reduces prereq conseq)))))

(defun parse-axioms(stats)
  (let-be [*known* stats
	   *rules* +read-rules+
	   lst (variants '(axiom ?x !- ?y))]
    (mappend #'parse-axiom lst)))
