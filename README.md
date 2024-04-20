This formalization project is developed with the [Coq proof assistant](https://coq.inria.fr/) to verify the mathematical theory -- the existence of non-principal arithmetical ultrafilters (NPAUF).

Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs.

It is suggested to run our code using a graphical Coq interface, such as CoqIDE for Windows, as it facilitates interactive checking of proof processes.

The code is developed in the CoqIDE (version 8.13.6) for 64 bit Windows and can be run at this version or higher ones.
CoqIDE (version 8.13.6) is available at [here](https://github.com/coq/platform/releases/download/2021.02.1/coq-platform-2021.02.1-installer-windows-x86_64.exe).
For other versions of Coq, click [here](https://coq.inria.fr/download).

The formalization comprises 8 (.v)files, whcih can be modified, run and compiled in CoqIDE. Here are the contents of each file:

mk_structure.v                 --  the formalization of definitions and axioms of Morse-Kelley (MK) axiomatic set theory.
mk_theorems.v                  --  the formalization and verification of theorems of MK.
operations_on_ω.v              --  the formal verification of fundamental operations (addition and multiplication) on natural numbers. 
infinite_sets.v                --  the formal verification of some properties involving infinite sets.
filter.v                       --  the formalization of concepts about filters (including ultrafilters, principal ultrafilters, free ultrafilters and more).
filter_extension.v             --  the formal verification of the Filter Extension Principle (FEP).
arithmetical_ultrafilter.v     --  the formalization of the concepts of arithmetical ultrafilter (AUF) and non-principal arithmetical ultrafilter (NPAUF).
existence_of_NPAUF.v           --  the formal verification of the existence of NPAUF.

The dependency of these files:

mk_structure.v  ->  mk_theorems.v  -> operations_on_ω.v  ->  infinite_sets.v  ->  filter.v  ->  filter_extension.v  &  arithmetical_ultrafilter.v  ->  existence_of_NPAUF.v

The file instruction.pdf is edited to introduce how to use these (.v)files in CoqIDE.
