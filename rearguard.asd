(in-package :asdf-user)

(defsystem "rearguard"
    :description "Theorem prover on the top of Modus"
    :version "1.0.1"
    :depends-on ("modus" "BonSavage")
    :components ((:file "packages")
		 (:file "RearGuard" :depends-on ("packages"))
		 (:file "compiler")))
