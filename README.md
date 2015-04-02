# formalCROM

This repository contains the reference implementation
of the role-based modeling language for Compartment Role Object Models (CROM)
and Compartment Role Object Instances (CROI),
as well as Constraint Models.
The implementation is kept simple, comprehensive, and
more importantly close to their formalization.

## Requirements

* Python >= 2.7.3 (see [Python Installation](https://www.python.org/downloads/release/python-279/) for more Information.)

## Structure of the Repository

The repository contains three files, whereas:

* **crom.py** contains the full reference implementation including classes,
    such as *CROM*, *CROI*, *ConstraintModel*, and auxiliary functions
* **cromtest.py** is a test suite build to test the implementation of all
    the axioms with both positive and negative cases.
* **cromexample.py** implements an example model with constraints, two of its instances,
    and evaluates their well-formedness, compliance, and validity, respectively

## Reference Implementation

The reference implementation is encapsulated in the **crom.py**
and contains the following classes:

* **CROM** representing a Compartment Role Object Model,
* **CROI** a Compartment Role Object Instance,
* **RoleGroups** the notion of a Role Group, and
* **ConstraintModel** a Constraint Model 

Please use this implementation, to apply, evaluate, and extend 
our formal role-based modeling language.

## Installation

Make sure to have a compatible Python version installed.

1. Clone the repository in to the desired folder.

    ```bash
    git clone https://github.com/Eden-06/formalCROM.git
    ```

2. Create and validate the example.

    ```bash
    python cromexample.py
    ```
    
## Version

1.0.0
