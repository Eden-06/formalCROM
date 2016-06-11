#!/usr/bin/env python
# -*- coding: UTF-8 -*-

"""cromexample.py: Contains the banking example provided in the paper."""

__author__ = "Thomas Kühn"
__copyright__ = "Copyright 2014"
__license__ = "MIT"
__version__ = "1.0.0"

from crom import *

# Example Model for the Bank

print "=== Example Model for the Bank ==="

bank=CROM(["Person","Company","Account"], # NT
          ["Customer","Consultant","CA","SA","Source","Target","MoneyTransfer"], # RT
          ["Bank","Transaction"], # CT
          ["own_ca","own_sa","advises","trans"], #RST
          [("Person","Consultant"),("Person","Customer"), ("Company","Customer"), 
           ("Account","Source"),("Account","Target"), ("Account","CA"), ("Account","SA"),
           ("Transaction","MoneyTransfer")], #fills
          {"Bank": ["Consultant","Customer","CA","SA","MoneyTransfer"],
           "Transaction": ["Source","Target"] }, #parts
          {"own_ca": ("Customer","CA"),
           "own_sa": ("Customer","SA"),
           "advises": ("Consultant","Customer"),
           "trans": ("Source","Target") } #rel
          )
print bank
if bank.wellformed():
	print " The bank model is a wellformed CROM"
else:
	print " The bank model is not wellformed"
print

# Role Groups in the Bank

print "=== Role Groups in the Bank ==="

bankaccounts=RoleGroup(["CA","SA"],1,1)
participants=RoleGroup(["Source","Target"],1,1)

print " bankaccounts={0}".format(bankaccounts)
print " participants={0}".format(participants)
print

# Constraint Model for the Bank

print "=== Constraint Model for the Bank ==="

c_bank=ConstraintModel( {"Bank": [ ( (1,inf),"Consultant"),((0,inf),bankaccounts) ],
                         "Transaction": [ ( (2,2),participants) ] }, #rolec
                        { "own_ca": ((1,1),(0,inf)),
                          "own_sa": ((1,inf),(0,inf)),
                          "advises": ((0,inf),(1,inf)),
                          "trans": ((1,1),(1,1)) }, #card
                        [ ("advises",irreflexive) ] #intra
                       )
print c_bank
if c_bank.compliant(bank):
	print "The constraint model is compliant to the CROM bank"
else:
	print "The constraint model is not compliant to the CROM bank"

print

# First Instance of the Bank Model

print "=== First Instance of the Bank Model ==="


bank1=CROI( ["Peter","Klaus","Google","Account_1","Account_2"], #n
            ["Cu_1","Cu_2","Cu_3","Ca","Sa","S","T","M"], #r
            ["bank","transaction"], #c
            {"Peter": "Person", "Klaus":"Person", "Google":"Company",
             "Account_1":"Account", "Account_2":"Account",
             "Cu_1":"Customer", "Cu_2":"Customer", "Cu_3":"Customer",
             "Ca":"CA", "Sa":"SA", "S":"Source", "T":"Target", 
             "M":"MoneyTransfer",
             "bank":"Bank", "transaction":"Transaction"}, #type1
            [("Klaus","bank","Cu_1"),("Google","bank","Cu_2"),("Peter","bank","Cu_3"),
             ("Account_2","bank","Ca"),("Account_1","bank","Sa"),
             ("transaction","bank","M"),
             ("Account_2","transaction","S"),("Account_2","transaction","T") ], #plays
            {("own_ca","bank"): [ ("Cu_1","Ca"), ("Cu_2",None), ("Cu_3",None) ],
             ("own_sa","bank"): [ ("Cu_1",None), ("Cu_2","Sa"), ("Cu_3",None)],
             ("advises","bank"): [ (None,"Cu_1"), (None,"Cu_2") , (None,"Cu_3") ],
             ("trans","transaction"): [ ("S","T") ]} #links
           )

print bank1

if bank1.compliant(bank):
	print " The first example is compliant to the CROM bank"
else:
	print " The first example is not compliant to the CROM bank"
	print " The following axioms were violated:"
	if not bank1.axiom6(bank):
		print "  axiom6"
	if not bank1.axiom7(bank):
		print "  axiom7"
	if not bank1.axiom8(bank):
		print "  axiom8"
	if not bank1.axiom9(bank):
		print "  axiom9"
	if not bank1.axiom10(bank):
		print "  axiom10"
	if not bank1.axiom11(bank):
		print "  axiom11"

print

# Second Instance of the Bank Model

print "=== Second Instance of the Bank Model ==="


bank2=CROI( ["Peter","Klaus","Google","Account_1","Account_2"], #n
            ["Con","Cu_1","Cu_2","Ca","Sa","S","T","M"], #r
            ["bank","transaction"], #c
            {"Peter": "Person", "Klaus":"Person", "Google":"Company",
             "Account_1":"Account", "Account_2":"Account",
             "Con":"Consultant", "Cu_1":"Customer", "Cu_2":"Customer", 
             "Ca":"CA", "Sa":"SA", "S":"Source", "T":"Target", 
             "M":"MoneyTransfer",
             "bank":"Bank", "transaction":"Transaction"}, #type1
            [("Klaus","bank","Cu_1"),("Google","bank","Cu_2"),("Peter","bank","Con"),
             ("Account_2","bank","Ca"),("Account_1","bank","Sa"),
             ("transaction","bank","M"),
             ("Account_1","transaction","S"),("Account_2","transaction","T") ], #plays
            {("own_ca","bank"): [ ("Cu_1","Ca"), ("Cu_2",None) ],
             ("own_sa","bank"): [ ("Cu_1",None), ("Cu_2","Sa")],
             ("advises","bank"): [ (None,"Cu_1"), ("Con","Cu_2") ],
             ("trans","transaction"): [ ("S","T") ]} #links
           )

print bank2

if bank2.compliant(bank):
	print " The second example is compliant to the CROM bank"
else:
	print " The second example is not compliant to the CROM bank"
	print " The following axioms were violated:"
	if not bank2.axiom6(bank):
		print "  axiom6"
	if not bank2.axiom7(bank):
		print "  axiom7"
	if not bank2.axiom8(bank):
		print "  axiom8"
	if not bank2.axiom9(bank):
		print "  axiom9"
	if not bank2.axiom10(bank):
		print "  axiom10"
	if not bank2.axiom11(bank):
		print "  axiom11"

print

# Evaluation

print "=== Evaluation ==="

if c_bank.validity(bank,bank1):
	print " The first example is a valid model of the bank wrt to the constraint model"
else:
	print " The first example is an invalid model of the bank wrt to the constraint model"
	print " The following axioms were violated:"
	if not c_bank.axiom13(bank,bank1):
		print "  axiom13"
	if not c_bank.axiom14(bank,bank1):
		print "  axiom14"
	if not c_bank.axiom15(bank,bank1):
		print "  axiom15"
	if not c_bank.axiom16(bank,bank1):
		print "  axiom16"
		
print

if c_bank.validity(bank,bank2):
	print " The second example is a valid model of the bank wrt to the constraint model"
else:
	print " The second example is an invalid model of the bank wrt to the constraint model"
	print " The following axioms were violated"
	if not c_bank.axiom13(bank,bank2):
		print "  axiom13"
	if not c_bank.axiom14(bank,bank2):
		print "  axiom14"
	if not c_bank.axiom15(bank,bank2):
		print "  axiom15"
	if not c_bank.axiom16(bank,bank2):
		print "  axiom16"
						
print
