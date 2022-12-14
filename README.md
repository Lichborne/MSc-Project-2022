# MSc-Project-2022
Implementation and proofs related to the 2 qubit Grover's algorithm, and a general implementation of Grover's algorithm in QWire.

Please note that a significant portion was written while learning the language framework, and so can be primitive in places. Please see line 959+ of _Grover2QubitRotations.v_ for some resonably interesting proofs and especially _GroverGeneralImp.v_ for sufficiently adequately formulated code. Note, however, that well-formedness is not proven for all parts of the general implementation, as there was not sufficient time. 

Moreover, the reasoning behind many parts of the implementation is to do with the thesis for which the project was written. If interested, please inquire about the thesis at bmf21@ic.ac.uk. 

Requires QWire, version as of June 2022. https://github.com/inQWIRE/QWIRE 
QWire relies on QuantumLib: https://github.com/inQWIRE/QuantumLib
Coq versions supported are 8.12 - 8.15. Company Coq in Proof General is suggested due to unicode support. 

## Files:

**_\_CoqProject_** includes the files that need to be compiled from QWire in order for this project to compile, commented out, 
and the files in the project in the order which they are to be compiled. The last two supplementary files, QFT.v and NotGrover2QubitGeneral
are also not included in the compilation, as they are not key parts of the project, but they do compile. **AFTER_TIME EDIT: The standard QWire makefile is to be used with coq's 'make' command to compile using this project file.**

**_\CoqMakefile and CoqMakefile.conf_ and Makefile** are **are not my product** they are taken from QWire and should be used to compile using the project file described above, added here **AFTER TIME** for convenience and clarification. Now with make a simple make will suffice, can be done independent but only subsequent to compiling QWire.

**_Grover2QubitBasic.v_** includes the implementation for an verification of Grover's algogithm for two qubits, one solution, and a single rotation.

**_Grover2QubitTotal.v_** includes the implementation for and verification of Grover's algorithm for two qubits, at least one and at most three solutions, and a single rotation

**_Grover2QubitRotations.v_** includes the implementation for Grover's algorithm for two qubits, at least one and at most three solutions, and an arbitrary number of rotations, as well as proof of the equivalence of the matrix expressions which the implementation should denote and the correctness condition for one of the implemented oracles, as well as the proof of denotational equivalence assuming the compositionality of denotations.

**_GroverGeneralImp.v_** contains an implementation of grover's algorithm for any number of qubits on a state space double the size, and an arbitrary number of rotations.

**SinAsinRules.v_** simply contains the only four specific axioms laid down for the project, which relate to some evaluations of the arcsine function. 

## Additional:

**_NotGrover2QubitGeneral.v_** contains an implementaiton of Grover's algorithm using improved oracles that use both information about both the turth and the falseness of evaluations of the boolean function on elements.

**_QFT.v_** contains implementations borrowed from SQIR and QWIRE to construct a lemma and begina proof for the correctness of the controll rotation operation in the relevant formulation of the Quantum Fourier Transform.
