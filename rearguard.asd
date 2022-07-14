(in-package :asdf-user)

(defsystem "RearGuard"
    :description "Theorem prover on top of Modus"
    :version "0.9"
    :depends-on ("Modus" "BonSavage")
    :components ((:file "packages")
		 (:file "RearGuard" :depends-on ("packages"))))
