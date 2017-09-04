#!/usr/bin/env python
# -*- coding: UTF-8 -*-

"""cromexample.py: Contains the banking example provided in the paper."""

__author__ = "Thomas Kühn"
__copyright__ = "Copyright 2014"
__license__ = "MIT"
__version__ = "1.0.3"

from crom_i import *


# Example Model for the Bank

print "=== Example Model for the Bank ==="

bank=CROM_I(["Person","Male","Female","Company","Account"], # NT
          ["Customer","Consultant","CA","SA","Source","Target","MoneyTransfer","CC","PremiumCustomer"], # RT
          ["Bank","Transaction","RetailBank","BusinessBank"], # CT
          ["own_ca","own_sa","advises","trans","own_cc"], #RST
          [#Bank
           ("Person","Bank","Consultant"),("Person","Bank","Customer"), ("Company","Bank","Customer"),
           ("Bank","Bank","Customer"),
           ("Account","Bank","CA"), ("Account","Bank","SA"), ("Transaction","Bank","MoneyTransfer"),
           #Transaction
           ("Account","Transaction","Source"),("Account","Transaction","Target"),
           #RetailBank
           ("Person","RetailBank","Customer"),("Account","RetailBank","CC"), ("Account","RetailBank","SA"),("Account","RetailBank","CA"),
           ("Person","RetailBank","Consultant"), ("Transaction","RetailBank","MoneyTransfer"),
           #BusinessBank
           ("Company","BusinessBank","PremiumCustomer"), ("Company","BusinessBank","Customer"),
           ("Bank","BusinessBank","PremiumCustomer"), ("Bank","BusinessBank","Customer"),
           ("Account","BusinessBank","SA"),("Account","BusinessBank","CA"), ("Person","BusinessBank","Consultant"),
           ("Transaction","BusinessBank","MoneyTransfer") ], #fills
          {#Bank
           ("own_sa","Bank"): ("Customer","SA"), ("own_ca","Bank"): ("Customer","CA"), ("advises","Bank"): ("Consultant","Customer"),
           #Transaction
           ("trans","Transaction"): ("Source","Target"),
           #RetailBank
           ("own_cc","RetailBank"): ("Customer","CC"), 
           ("own_sa","RetailBank"): ("Customer","SA"),  ("own_ca","RetailBank"): ("Customer","CA"), ("advises","RetailBank"): ("Consultant","Customer"),
           #BusinessBank
           ("own_sa","BusinessBank"): ("Customer","SA"), ("own_ca","BusinessBank"): ("Customer","CA"), ("advises","BusinessBank"): ("Consultant","Customer")
            },  #rel
          [("Male","Person"), ("Female","Person")], #prec_nt
          [("RetailBank","Bank"), ("BusinessBank","Bank")]  #prec_ct
          )
print bank

if bank.wellformed():
	print " The bank model is a wellformed CROM"
else:
	print " The bank model is not wellformed"
	print " The following axioms were violated:"
	if not bank.axiom1():
		print "  axiom1"
	if not bank.axiom2():
		print "  axiom2"
	if not bank.axiom3():
		print "  axiom3"
	if not bank.axiom4():
		print "  axiom4"
	if not bank.axiom5():
		print "  axiom5"
	if not bank.axiom6():
		print "  axiom6"
	if not bank.axiom7():
		print "  axiom7"
	if not bank.axiom8():
		print "  axiom8"
print

# Role Groups in the Bank

print "=== Role Groups in the Bank ==="

bankaccounts=RoleGroup(["CA","SA"],1,1)
participants=RoleGroup(["Source","Target"],1,1)
retailaccounts=RoleGroup(["CC","CA","SA"],1,1)
premiumimpl=RoleGroup([RoleGroup(["PremiumCustomer"],0,0),"Customer"],1,2)
#accountimpl=QuantifiedGroup(...)

print " bankaccounts={0}".format(bankaccounts)
print " participants={0}".format(participants)
print " retailaccounts={0}".format(retailaccounts)
print " premiumimpl={0}".format(premiumimpl)
print

print "=== Quantified Role Groups in the Bank ==="

pa=RoleGroup(["Source","Target"],1,1)
ba=RoleGroup(["CA","SA"],1,1)
l=Quantification("Transaction",1,-1,pa)
r=Quantification("Bank",1,-1,ba)
existentialimpl=QuantifiedGroup([QuantifiedGroup([l],0,0),r],1,2)


#accountimpl=QuantifiedGroup(...)

print " existentialimpl={0}".format(existentialimpl)
print

# Constraint Model for the Bank
print "=== Constraint Model for the Bank ==="
c_bank=ConstraintModel_I( {"Bank": [ ( (1,inf),"Consultant"),((0,inf),bankaccounts) ],
                       "Transaction": [ ( (2,2),participants) ],
                       "RetailBank": [ ((0,inf), retailaccounts) ],
                       "BusinessBank": [((0,inf), premiumimpl) ] }, #rolec
                      { ("own_ca","Bank"): ((1,1),(0,inf)),
                        ("own_sa","Bank"): ((1,inf),(0,inf)),
                        ("advises","Bank"): ((0,inf),(1,inf)),
                        ("trans","Transaction"): ((1,1),(1,1)),
                        ("own_cc","RetailBank"): ((1,1),(0,1)),
                        ("advises","BusinessBank"): ((1,1),(1,inf)) }, #card
                      [ ("advises","Bank",irreflexive) ], #intra
                      [ ("own_ca","Bank",exclusion,"own_sa")], #inter
                      [existentialimpl]  #grolec
                     )
print c_bank
if c_bank.compliant(bank):
	print "The constraint model is compliant to the CROM bank"
else:
	print "The constraint model is not compliant to the CROM bank"
	if not c_bank.axiom10(bank):
		print "  axiom10"
	if not c_bank.axiom11(bank):
		print "  axiom11"
	if not c_bank.axiom12(bank):
		print "  axiom12"
	if not c_bank.axiom13(bank):
		print "  axiom13"

print

# First Instance of the Bank Model

bank1=CROI_I( ["Peter","Klaus","Google","Account_1","Account_2"], #n
            ["Cu_1","Cu_2","Cu_3","Ca","Sa","S","T","M","Con","Con1"], #r
            ["bank","transaction"], #c
            {"Peter": "Person", "Klaus":"Person", "Google":"Company",
             "Account_1":"Account", "Account_2":"Account",
             "Cu_1":"Customer", "Cu_2":"Customer", "Cu_3":"Customer",
             "Ca":"CA", "Sa":"SA", "S":"Source", "T":"Target", 
             "M":"MoneyTransfer", "Con":"Consultant", "Con1":"Consultant",
             "bank":"Bank", "transaction":"Transaction"}, #type1
            [("Klaus","bank","Cu_1"),("Google","bank","Cu_2"),("Peter","bank","Cu_3"),
             ("Account_2","bank","Ca"),("Account_1","bank","Sa"),
             ("transaction","bank","M"),("Klaus","bank","Con"),("Peter","bank","Con1"),
             ("Account_2","transaction","S"),("Account_2","transaction","T") ], #plays
            {("own_ca","bank"): [ ("Cu_1","Ca") ],
             ("own_sa","bank"): [ ("Cu_2","Sa") ],
             ("advises","bank"): [ ("Con","Cu_1") ],
             ("trans","transaction"): [ ("S","T") ]} #links
           )

# Second Instance of the Bank Model

bank2=CROI_I( ["Peter","Klaus","Google","Account_1","Account_2"], #n
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
            {("own_ca","bank"): [ ("Cu_1","Ca") ],
             ("own_sa","bank"): [ ("Cu_2","Sa")],
             ("advises","bank"): [ ("Con","Cu_2") ],
             ("trans","transaction"): [ ("S","T") ]} #links
           )

# Third Instance of the Bank Model

bank3=CROI_I( ["Peter","Klaus","Google","Account_1","Account_2","Account_3"], #n
            ["Con","Cu_1","Cu_2","Ca","Sa","S","T","M",
             "Cu_3","Cu_4", "Cu_5", "Con_2", "Con_3", "Con_4" , "Cc", "Pc"], #r
            ["bank","transaction","rb","bb"], #c
            {"Peter": "Person", "Klaus":"Person", "Google":"Company",
             "Account_1":"Account", "Account_2":"Account", "Account_3":"Account",
             "Con":"Consultant", "Con_2":"Consultant", "Con_3":"Consultant", "Con_4":"Consultant",
             "Cu_1":"Customer", "Cu_2":"Customer", "Cu_3":"Customer", "Cu_4":"Customer", "Cu_5":"Customer",
             "Ca":"CA", "Sa":"SA", "Cc":"CC", "Pc":"PremiumCustomer",
             "S":"Source", "T":"Target", 
             "M":"MoneyTransfer",
             "rb" : "RetailBank", "bb":"BusinessBank",
             "bank":"Bank", "transaction":"Transaction"}, #type1
            [("Klaus","bank","Cu_1"),("Google","bank","Cu_2"),("Peter","bank","Con"),
             ("Account_2","bank","Ca"),("Account_1","bank","Sa"),
             ("transaction","bank","M"),
             ("Account_1","transaction","S"),("Account_2","transaction","T"),             
             ("Klaus", "rb", "Cu_3" ), ("Peter", "rb", "Con_2" ), ("Account_3" , "rb", "Cc"),
             ("Klaus", "bb", "Con_3" ), ("Peter", "bb", "Con_4" ), ("Google", "bb", "Cu_4" ),
             ("Google", "bb", "Pc" ),  ("rb", "bb", "Cu_5" ) ], #plays
            {("own_ca","bank"): [ ("Cu_1","Ca") ],
             ("own_sa","bank"): [ ("Cu_2","Sa")],
             ("advises","bank"): [ ("Con","Cu_2") ],
             ("trans","transaction"): [ ("S","T") ],                
             ("own_cc", "rb"): [("Cu_3" , "Cc")],
             ("advises", "rb"): [("Con_2" , "Cu_3" ), ("Con_4" , "Cu_5" )],
             ("advises", "bb"): [("Con_3" , "Cu_4" ), ("Con_4" , "Cu_5" )] } #links
           )
           
# Fourth Instance of the Bank Model

bank4=CROI_I( ["Peter","Klaus","Google","Account_1","Account_2","Account_3"], #n
            ["Con","Cu_1","Cu_2","Ca","Sa","S","T","M",
             "Cu_3","Cu_4", "Cu_5", "Con_2", "Con_3", "Con_4" , "Cc", "Pc"], #r
            ["bank","transaction","rb","bb"], #c
            {"Peter": "Person", "Klaus":"Person", "Google":"Company",
             "Account_1":"Account", "Account_2":"Account", "Account_3":"Account",
             "Con":"Consultant", "Con_2":"Consultant", "Con_3":"Consultant", "Con_4":"Consultant",
             "Cu_1":"Customer", "Cu_2":"Customer", "Cu_3":"Customer", "Cu_4":"Customer", "Cu_5":"Customer",
             "Ca":"CA", "Sa":"SA", "Cc":"CC", "Pc":"PremiumCustomer",
             "S":"Source", "T":"Target", 
             "M":"MoneyTransfer",
             "rb" : "RetailBank", "bb":"BusinessBank",
             "bank":"Bank", "transaction":"Transaction"}, #type1
            [("Klaus","bank","Cu_1"),("Google","bank","Cu_2"),("Peter","bank","Con"),
             ("Account_1","bank","Ca"),("Account_1","bank","Sa"),
             ("transaction","bank","M"),
             ("Account_1","transaction","S"),("Account_3","transaction","T"),             
             ("Klaus", "rb", "Cu_3" ), ("Klaus", "rb", "Con_2" ), ("Account_3" , "rb", "Cc"),
             ("Klaus", "bb", "Con_3" ), ("Peter", "bb", "Con_4" ), ("Google", "bb", "Cu_4" ),
             ("Google", "bb", "Pc" ),  ("rb", "bb", "Cu_5" ) ], #plays
            {("own_ca","bank"): [ ("Cu_1","Ca") ],
             ("own_sa","bank"): [ ("Cu_1","Sa")],
             ("advises","bank"): [ ("Con","Cu_2") ],
             ("trans","transaction"): [ ("S","T") ],                
             ("own_cc", "rb"): [("Cu_3" , "Cc")],
             ("advises", "rb"): [("Con_2" , "Cu_3" ), ("Con_4" , "Cu_5" )],
             ("advises", "bb"): [("Con_3" , "Cu_4" ), ("Con_4" , "Cu_4" )] } #links
           )           
           
test_crois=[ ("first",bank1), ("second",bank2), ("third",bank3), ("fourth",bank4) ]

# Compliance

print "=== Compliance ==="
print 

for s,b in test_crois:
	print b
	if b.compliant(bank):
		print " The {0} example is compliant to the CROM bank".format(s)
	else:
		print " The {0} example is not compliant to the CROM bank".format(s)
		print " The following axioms were violated:"
		if not b.axiom6(bank):
			print "  axiom6"
			print b.axiom6.__doc__
		if not b.axiom7(bank):
			print "  axiom7"
			print b.axiom7.__doc__		
		if not b.axiom8(bank):
			print "  axiom8"
			print b.axiom8.__doc__		
		if not b.axiom9(bank):
			print "  axiom9"
			print b.axiom9.__doc__		
	print



# Evaluation

print "=== Evaluation ==="

for s,b in test_crois:
	if c_bank.validity(bank,b):
		print " The {0} example is a valid model of the bank wrt to the constraint model".format(s)
	else:
		print " The {0} example is an invalid model of the bank wrt to the constraint model".format(s)
		print " The following axioms were violated:"
		if not c_bank.axiom14(bank,b):
			print "  axiom14"
			print c_bank.axiom14.__doc__
		if not c_bank.axiom15(bank,b):
			print "  axiom15"
			print c_bank.axiom15.__doc__
		if not c_bank.axiom16(bank,b):
			print "  axiom16"
			print c_bank.axiom16.__doc__
		if not c_bank.axiom17(bank,b):
			print "  axiom17"
			print c_bank.axiom17.__doc__
		if not c_bank.axiom18(bank,b):
			print "  axiom18"
			print c_bank.axiom18.__doc__
		if not c_bank.axiom19(bank,b):
			print "  axiom19"
			print c_bank.axiom19.__doc__
		if not c_bank.axiom20(bank,b):
			print "  axiom20"
			print c_bank.axiom20.__doc__
	print

