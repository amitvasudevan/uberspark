Introduction
============

This folder contains the überSpark high-level assume-guarantee composition proofs encoded in TLA+.

src-pcode/ 
    This sub-folder contains the pseudo-code for the system model written in plain (restructured) text


TLA+ Toolbox
------------

The Toolbox can be downloaded from <https://github.com/tlaplus/tlaplus/releases/tag/v1.7.0>. For Linux, run the 'toolbox' executable. (More instructions forthcoming)

Select File -> Open Spec -> Add New Spec
Set Root-module file to uberspark/proofs/tla/toy.tla and have it import existing models.
Note: Importing the model is not working for me right now, so copy over the Model_1 folder from uberspark/proofs/tla/ to your project folder, or manually fill in the constant values to a new model.


