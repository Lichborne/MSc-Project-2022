# MSc-Project-2022
Implementation and proofs related to the 2 qubit Grover's algorithm, and a general implementation of Grover's algorithm in QWire.

Requires QWire, version as of June 2022. https://github.com/inQWIRE/QWIRE 
QWire relies on QuantumLib: https://github.com/inQWIRE/QuantumLib
Coq versions supported are 8.12 - 8.15. Company Coq in Proof General is suggested due to unicode support. 

Files:

_CoqProject includes the files that need to be compiled from QWire in order for this project to compile, commented out, 
and the files in the project in the order which they are to be compiled. The last two supplementary files, QFT.v and NotGrover2QubitGeneral
are also not included in the compilation, as they are not key parts of the project, but they do compile.

Grover2QubitBasic.v includes the implementation for an verification of Grover's algogithm for two qubits, one solution, and a single rotation.

Grover2QubitTotal.v includes the implementation for and verification of Grover's algorithm for two qubits, at least one and at most three solutions, and a single rotation

Grover2QubitRotations.v includes the implementation for Grover's algorithm for two qubits, at least one and at most three solutions, and an arbitrary number of rotations, as well as proof of the equivalence of the matrix expressions which the implementation should denote and the correctness condition for one of the implemented oracles, as well as the proof of denotational equivalence assuming the compositionality of denotations.

GroverGeneralImp.v contains an implementation of grover's algorithm for any number of qubits on a state space double the size, and an arbitrary number of rotations.


Additional:

NotGrover2QubitGeneral.v contains an implementaiton of Grover's algorithm using improved oracles that use both information about both the turth and the falseness of evaluations of the boolean function on elements.

QFT.v contains implementations borrowed from SQIR and QWIRE to construct a lemma and begina proof for the correctness of the controll rotation operation in the relevant formulation of the Quantum Fourier Transform.
