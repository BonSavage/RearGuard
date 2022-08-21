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
    (true (?x and ?y)))
   
   (rule
    (or
     (false ?x)
     (false ?y))
    (false (?x and ?y)))
   
   (rule
    (or
     (true ?x)
     (true ?y))
    (true (?x or ?y)))
   
   (rule
    (and
     (false ?x)
     (false ?y))
    (false (?x or ?y)))

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
   '(consequence ?x of ?x)
   '(prerequisite ?x of ?x)
   ))

(defconstant +simplify-rules+
  (list

   (rule
    (or (consequence ?x of ?z)
	(consequence ?x of ?y))
    (consequence ?x of (?z and ?y))) ;Warning! This pattern is applicative. (consequence ?x of ?x) gives infinite recursion. Althrough, with lists it works quite well.
   
   (rule
    (or (prerequisite ?x of ?z)
	(prerequisite ?x of ?y))
    (prerequisite ?x of (?z or ?y)))
   
   (rule (consequence ?x of ?y)
	 (prerequisite (not ?y) of (not ?x)))
   
   (rule (prerequisite ?x of ?y)
	 (consequence (not ?y) of (not ?x)))
   
   (rule (and
  	  (consequence ?x of ?y)
  	  (consequence ?x of ?z))
  	 (consequence ?x of (?y or ?z)))
   
   (rule (and
  	  (prerequisite ?x of ?y)
 	  (prerequisite ?x of ?z))
	 (prerequisite ?x of (?y and ?z)))
   ))

(defun simplify(stat)
  (let-be [*rules* +simplify-rules+
	   *known* +simplify-known+
	   *sweeped* nil]
    (evaluate stat)))

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
