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

A model is run by TLC Model Checker -> Run Model, pressing F11, or clicking the green arrow near the top of left of the window after opening a model.


TLA+ Command-line Tools
-----------------------

Multiple ways to do this exist. The one I am trying right now is from <https://github.com/hwayne/tlacli>. You need Java, Python 3, and pip. To install, run:
::

pip install tlacli

Make sure the `tlacli` script is in your path.

To check the model, run (from the proofs/tla directory):
::

tlacli check --cfg uSpark.cfg uSpark.tla

After altering the pluscal algorithm, to re-translate and parse, run:
::

tlacli translate --cfg uSpark.tla

Constants can be altered in uSpark.cfg. More instructions on invariants, how to alter the model, and TLAPS (the proof system) forthcoming.
