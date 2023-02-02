;;;; RearGuard theorem prover
;;;; Complete rewrite on the top of Modus
;;;; 14.07.2022
;;;; Maxim "BonSavage" Kirillov

(in-package :rearguard)

;;;Base inference

(defparameter +general-known+
  (list
   '(eq ?x ?x) ;;Must be op
   '(true true)
   '(false false)
   ))

   
(defparameter +general-rules+
  (list
   
   ;;Expressions
   (rule
    (axiom ?x !- ?y)
    (reduces ?x ?y))
   
   (rule
    (axiom ?x !- ?y)
    (applicates ?x ?y))
   
   (rule (def ?x <=> ?y)
	 (axiom ?x !- ?y))
   (rule (def ?x <=> ?y)
	 (axiom ?y !- ?x))
   
   ;;Operators
   (rule
    (and
     (true ?x)
     (true ?y))
    (true (and ?x ?y)))
   
   (rule
    (or
     (false ?x)
     (false ?y))
    (false (and ?x ?y)))
   
   (rule
    (or
     (true ?x)
     (true ?y))
    (true (or ?x ?y)))
   
   (rule
    (and
     (false ?x)
     (false ?y))
    (false (or ?x ?y)))

   ;;Consequences and prerequisites

   (rule
    (modus:lisp-value simplify (consequence ?x of ?y))
    (consequence ?x of ?y))

   (rule
    (modus:lisp-value simplify (prerequisite ?x of ?y))
    (prerequisite ?x of ?y))
   
   ;;Inference
   
   (rule
    (false ?x)
    (true (not ?x)))
   
   (rule
    (true ?x)
    (false (not ?x)))
   
   (rule
    (or
     (known ?x)
     (and
      (applicates ?y ?z)
      (consequence ?x of ?z)
      (true ?y)))
    (true ?x)) ;This rule is applicable for negation as well
   
   (rule
    (or
     (known (not ?x))
     (and
      (applicates ?y ?z)
      (prerequisite ?x of ?y)
      (false ?z)))
    (false ?x))
   
   ;;Unsafe
   (rule
    (reduces ?x ?y)
    (applicates (not ?y) (not ?x)))
   
   (rule (applicates ?x ?y)
	 (reduces (not ?y) (not ?x)))
   ))

(defparameter *known* +general-known+)
(defparameter *rules* +general-rules+)

;;Simplify

(defconstant +simplify-known+
  (list
   '(eq ?a ?a)
   '(consequence ?x of ?x)
   '(prerequisite ?x of ?x)
   ))

(defconstant +simplify-rules+
  (list

   (rule
    (and (none (eq ?x (and ?z ?y)))
	 (or (consequence ?x of ?z)
	     (consequence ?x of ?y)))
    (consequence ?x of (and ?z ?y))) ;Warning! This pattern is applicative. (consequence ?x of ?x) gives infinite recursion. Althrough, with lists it works quite well.
   
   (rule
    (and (none (eq ?x (or ?z ?y)))
	 (or (prerequisite ?x of ?z)
	     (prerequisite ?x of ?y)))
    (prerequisite ?x of (or ?z ?y)))
   
   (rule (consequence ?x of ?y)
	 (prerequisite (not ?y) of (not ?x)))
   
   (rule (prerequisite ?x of ?y)
	 (consequence (not ?y) of (not ?x)))
   
   (rule (and
	  (none (eq ?x (or ?y ?z)))
  	  (consequence ?x of ?y)
  	  (consequence ?x of ?z))
  	 (consequence ?x of (or ?y ?z)))
   
   (rule (and
	  (none (eq ?x (and ?y ?z)))
  	  (prerequisite ?x of ?y)
 	  (prerequisite ?x of ?z))
	 (prerequisite ?x of (and ?y ?z)))
   ))

(defun simplify(stat)
  (if (and nil (eq (second stat) (fourth stat))) ;Consequence or prerequisite of itself
      (values nil t)
      (let-be [*rules* +simplify-rules+
	       *known* +simplify-known+
	       *sweeped* nil]
	(evaluate stat))))

;;;Inference

(defmacro with-axioms ((&rest rules) &body forms)
  `(let ((*known* (append ',rules *known*)))
     ,@forms))

(defmacro with-environment
    (known
     rules
     facts
     &body forms)
  `(let ((*known* (append (append ,facts ,known) *known*))
	 (*rules* (append ,rules *rules*)))
     ,@forms))

(defun infer(stat)
  (let-be [(_ any-true) (evaluate `(true (not ,stat)))
	   (_ any-false) (evaluate `(false (not ,stat)))]
    (cond
      ((and any-true any-false) (error "Contradiction found!"))
      (any-true 'false)
      (any-false 'true)
      (t stat))))

;;Debug

(defun variants(stat)
  (awith (evaluate stat)
    (mapcar (lambda (sub) (sublis sub stat)) it)))

(defun print-variants(stat)
  (awith (variants stat)
    (dolist (elem it)
      (format t "~a ~&" elem))))
