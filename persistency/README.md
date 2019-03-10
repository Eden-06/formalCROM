# Persistence Transformation

This folder contains the reference implementation
of the persitence transformation for centext-dependent domain models, i.e., the Compartment Role Object Models (CROM).
It features the Transformation algorithm for CROM and corresponding Constraint Models, as well as the Restriction algorithm for Compartment Role Object Instances (CROI).
The implementation is kept simple, comprehensive, and
more importantly close to their formalization.


## Requirements

* Python >= 2.7.3 (see [Python Installation](https://www.python.org/downloads/release/python-279/) for more Information.)

## Structure of the Repository

The repository contains three files, whereas:

* **crompersistency.py** contains the full reference implementation including the persitence annotation,
    the transformation algorithm, as well as the restriction algorithm.
* **crompersistencytest.py** is a test suite build to test the implementation of
    the transformation and restriction including testing the three theorems from the paper.
* **crompersistencyexample.py** implements the fire alarm example model with constraints,
    one instance and evaluates the well-formedness, compliance, and validity of the persisted CROM,
    persisted Constraint Model, and persisted CROI, respectively.

## Reference Implementation

The reference implementation is encapsulated in the **crompersistency.py**
and contains the following classes:

* **PersistenceAnnotation** representing an annotatation of a CROM,
* **transformation** implements the persistence transformation from the paper, and
* **restriction** implements the CROI restriction from the paper.

Please use this implementation, to apply, evaluate, and extend 
our persistence transformation.

## Installation

Make sure to have a compatible Python version installed.

1. Clone the repository in to the desired folder.

    ```bash
    git clone https://github.com/Eden-06/formalCROM.git
    ```

2. Move into the persistency folder and execute the running example.

    ```bash
    cd persistency
    python cromepersistencyexample.py
    ```
    
## Version

1.0.0
