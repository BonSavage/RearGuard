;;;RearGuard to modus compiler
(in-package :rearguard)

(defun simple-negate(expr)
  (if (eq (car expr) 'not)
      (cadr expr)
      (list 'not expr)))

(defun negate-expr(expr fn)
  (if (listp expr)
      (let-be [closure (lambda (elem) (negate-expr elem fn))]
	(case (car expr)
	  (and (funcall fn (cons 'or (mapcar #'simple-negate (cdr expr)))))
	  (or (funcall fn (cons 'and (mapcar #'simple-negate (cdr expr)))))
	  (not (funcall fn (cadr expr)))
	  (t (list 'false expr))))
      (list 'false expr)))

(defun compile-prerequisite(pre)
  (if (listp pre)
      (case (car pre)
	(and (cons 'modus:and (mapcar #'compile-prerequisite (cdr pre))))
	(or (cons 'modus:or (mapcar #'compile-prerequisite (cdr pre))))
	(not (negate-expr (cadr pre) #'compile-prerequisite))
	(t (list 'true pre)))
      (list 'true pre)))

(defun precompile-consequence(conseq)
  (compile-prerequisite conseq))

(defun process-reduction-conseq(conseq)
  (case (car conseq)
    (true (cons 'newly-true (cdr conseq)))
    (false (cons 'newly-false (cdr conseq)))))

(defun compile-reduction(red)
  (let-be [(list _ prerequisite precompiled-consequence) red
	   conseq-processed (modus::expr-predicate (process-reduction-conseq precompiled-consequence))
	   prerequisite-processed (modus::expr-predicate (list 'modus:and (compile-prerequisite prerequisite) (list 'modus:none precompiled-consequence)))]
    (modus::make-rule prerequisite-processed conseq-processed)))

(defun compile-application(conc)
  (destructuring-bind (type prerequisite precompiled-consequence) conc
    (modus::make-rule
     (modus::expr-predicate (compile-prerequisite prerequisite))
     (modus::expr-predicate precompiled-consequence))))

(defun compile-conclusion(conc)
  (funcall
   (case (car conc)
     (applicates #'compile-application)
     (reduces #'compile-reduction))
   conc))

(defun decompile-expr(compiled-expr)
  (if (atom compiled-expr)
      compiled-expr
      (case (car compiled-expr)
	((newly-true true) (cadr compiled-expr))
	(false (simple-negate (decompile-expr (cadr compiled-expr))))
	((and or) (cons (car compiled-expr)
			(mapcar #'decompile-expr (cdr compiled-expr))))
	(t compiled-expr))))

(defun complement-type(type)
  (case type
    (reduces 'applicates)
    (applicates 'reduces)))

(defun compile-to-rules(conc)
  (let-be [(list type prerequisite consequence) conc
	   compiled (precompile-consequence consequence)]
    (case (car compiled)
      (and (mappend (lambda (expr) (compile-to-rules `(,type ,prerequisite ,(decompile-expr expr)))) (cdr compiled)))
      (or
       (let-be [(list op operand1 operand2) compiled
		prereq (compile-prerequisite prerequisite)]
	 (mappend
	  #'compile-to-rules
	  (list
	   (list
	    type
	    (decompile-expr `(and (false ,(decompile-expr operand1)) ,prereq))
	    (decompile-expr operand2))
	   (list
	    type
	    (decompile-expr `(and (false ,(decompile-expr operand2)) ,prereq))
	    (decompile-expr operand1))))))
      (t (list (compile-conclusion (list type prerequisite compiled)))))))

(defun compile-conclusions(rules)
  (remove-duplicates (mappend #'compile-to-rules rules) :test #'equalp))
