;;;; RearGuard theorem prover
;;;; Complete rewrite on the top of Modus
;;;; 14.07.2022: v. 1
;;;; 19.02.2023: v. 2
;;;; Maxim "BonSavage" Kirillov

(in-package :rearguard)

;;;Inference of applicative consequences

(defparameter +inference-known+
  (list
   '(eq ?x ?x) ;;Must be op
   '(true true)
   '(false false)
   ;'(applicates (and ?x ?y) ?x)
   ;'(applicates (and ?x ?y) ?y)
   ))

   
(defparameter +inference-rules+
  (list
   
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
     (and
      (applicates ?y ?z)
      (consequence ?x of ?z)
      (true ?y))
     (true ?x)) ;This rule is applicable for negation as well

   
   ;(rule
   ; (or
   ;  (known (not ?x))
   ;  (and
   ;   (applicates ?y ?z)
   ;   (prerequisite ?x of ?y)
   ;   (false ?z)))
   ; (false ?x))
   
   ))

(defparameter *known* +inference-known+)
(defparameter *rules* +inference-rules+)

;;Inference of reductive consequences

;;Reader

(defconstant +read-known+
  '(
    (reduces (and ?x ?y) ?x)
    (reduces (and ?x ?y) ?y)
    (true true)
   ))

(defconstant +read-rules+
  (list

   ;(rule
   ; (axiom ?x !- ?y)
   ; (reduces ?x ?y)) ;Applications successfully deals with it

   (rule
    (axiom ?x !- ?y)
    (applicates ?x ?y))

   (rule
    (axiom ?x <->> ?y)
    (reduces ?x ?y))

   (rule
    (axiom ?x <->> ?y)
    (applicates ?y ?x))
   
   (rule (def ?x <=> ?y)
	 (axiom ?x !- ?y))
   
   (rule (def ?x <=> ?y)
	 (axiom ?y !- ?x))
   
   (rule
    (reduces ?x ?y)
    (applicates (not ?y) (not ?x)))
   
   (rule
    (applicates ?x ?y)
    (reduces (not ?y) (not ?x)))
   ))

(defun parse-applications(states)
  (let-be [*known* states
	   *rules* +read-rules+]
    (variants '(applicates ?x ?y))))

(defun parse-reductions(states)
  (let-be [*known* (append +read-known+ states)
	   *rules* +read-rules+]
    (variants '(reduces ?x ?y))))

(defun reduce-known(known reductions)
  (let-be [*rules* +read-rules+
	   *known* (append known reductions)
	   *sweeped* nil]
    (append
     known
     (variants '(known ?x))
     (mappend
      (lambda (fact)
	(let-be [bindings (evaluate `(=> ,(second fact) ?x))
		 res (mapcar (alexandria:rcurry #'sublis '(known ?x)) bindings)]
	  res))
      known))))

(defparameter +reduce-rules+
  (list

   (rule
    (true ?x)
    (reduces (or ?x ?y) ?y))

   (rule
    (true ?y)
    (reduces (or ?x ?y) ?x))

   ;(rule
   ; (known ?x)
   ; (true ?x))

   (rule
    (and
     (true ?x)
     (true ?y))
    (true (and ?x ?y)))
   
   (rule
    (or
     (true (not ?x))
     (true (not ?y)))
    (true (not (and ?x ?y))))
   
   (rule
    (or
     (true ?x)
     (true ?y))
    (true (or ?x ?y)))
   
   (rule
    (and
     (true (not ?x))
     (true (not ?y)))
    (true (not (or ?x ?y))))

   (rule
    (and
     (or
      (and
       (reduces ?y ?x)
       (true ?y))
      (true ?x))
     (none (true ?x)))
    (newly-true ?x))

   ))

(defun reduce-true(known reductions)
  (let-be [*rules* +reduce-rules+
	   *known* (append reductions (mapcar (lambda (stat) (list 'true (second stat))) known) *known*)
	   *sweeped* nil]
    (alet ((true nil) (newly-true nil))
      (let-be [*known* (append newly-true *known*)
	       newly-true (remove-duplicates
			   (mapcar (alexandria:rcurry #'sublis '(true ?x))
				   (evaluate '(newly-true ?x)))
			   :test #'equalp)
	       true (append newly-true true)]
	(if newly-true
	    (self true newly-true)
	    true)))))


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
  (let-be [*rules* +simplify-rules+
	   *known* +simplify-known+
	   *sweeped* nil]
    (evaluate stat)))
;;;Inference

(defmacro with-axioms ((&rest rules) &body forms)
  `(let ((*known* (append ',rules *known*)))
     ,@forms))

(defstruct environment
  (reductions)
  (applications))

(defmacro define-environment(name &rest axioms)
  `(defconstant ,name (make-environment
		       :applications (parse-applications ',axioms)
		       :reductions (parse-reductions ',axioms))))

(defmacro with-environment
    (env
     known
     &body forms)
  `(let-be [*known* (append +inference-known+ (environment-applications ,env) (reduce-true ',known (environment-reductions ,env)))]
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
    (filtering-map (lambda (sub) (when sub (sublis sub stat))) it)))

(defun print-variants(stat)
  (awith (variants stat)
    (dolist (elem it)
      (format t "~a ~&" elem))))
