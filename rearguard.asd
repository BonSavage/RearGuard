(in-package :asdf-user)

(defsystem "rearguard"
    :description "Theorem prover on top of Modus"
    :version "0.9"
    :depends-on ("modus" "BonSavage")
    :components ((:file "packages")
		 (:file "RearGuard" :depends-on ("packages"))))
