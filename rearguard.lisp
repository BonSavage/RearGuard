;;;; RearGuard theorem prover
;;;; Complete rewrite on the top of Modus
;;;; 14.07.2022
;;;; Maxim "BonSavage" Kirillov

(in-package :rearguard)

;;;Base inference

(defparameter *known*
  (list
   '(eq ?x ?x) ;;Must be op
   '(true true)
   '(false false)
   ))

   
(defparameter *rules*
  (list
   
   ;;Expressions
   (rule
    (op ?x !- ?y)
    (reduces ?x ?y))
   (rule
    (op ?x !- ?y)
    (applicates ?x ?y))
   
   (rule (op ?x <=> ?y)
	 (op ?x !- ?y))
   (rule (op ?x <=> ?y)
	 (op ?y !- ?x))
   
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
    (lisp-value simplify (consequence ?x of ?y))
    (consequence ?x of ?y))

   (rule
    (lisp-value simplify (prerequisite ?x of ?y))
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
    (consequence ?x of (?z and ?y)))
   
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
	   *known* +simplify-known+]
    (rule-inference (expr-predicate stat))))

;;;Inference

(defun infer(stat)
  (let-be [bnds-list (rule-inference (expr-predicate `(?x (not ,stat))))
	   ?xs (mapcar (lambda (bnds) (cdr (assoc '?x bnds))) bnds-list)]
    (cond
      ((find 'true ?xs) 'false)
      ((find 'false ?xs) 'true)
      (t stat))))
