#!/usr/bin/env python
# -*- coding: UTF-8 -*-

"""crompersistencyexample.py: Contains the fire alarm example provided in the paper."""

__author__ = "Thomas Kühn"
__copyright__ = "Copyright 2014"
__license__ = "MIT"
__version__ = "1.0.3"

from crom import *
from crompersistency import *

def testtheorems(pannotation,fmodel,fcm):
	print " Test Persistence Annotations:"
	print "  "+str(pannotation)
	ext=compute_ext(fmodel,fcm)	
	pfills=pannotation.compute_fills(fmodel,fcm,ext)
	assert pfills <= fmodel.fills
	prel=pannotation.compute_rel(fmodel,fcm,pfills)
	assert set( prel.iterkeys() ) <= set( fmodel.rel.iterkeys() )
	poccur=pannotation.compute_occur(fcm,pfills,prel)
	assert set( poccur.iterkeys() ) <= set( fcm.rolec.iterkeys() )
	pcard=pannotation.compute_card(fcm,pfills,prel)
	assert set( pcard.iterkeys() ) <= set( fcm.card.iterkeys() )	
	#Theorem 1
	pmodel,pcm = transformation(fmodel,fcm,pannotation)
	print "  Test persisted CROM well-formedness"
	assert pmodel.wellformed()
	print "  Test persisted Constraint Model compliance to persisted CROM"
	assert pcm.compliant(pmodel)
	#Theorem 2
	pinstance=restriction(pmodel,finstance)
	print "  Test restricted CROI compliance to persisted CROM"
	assert pinstance.compliant(pmodel)
	print "  Test restricted CROI validity to persisted Constraint Model"
	assert pcm.validity(pmodel,pinstance)
	#Theorem 3
	qinstance=restriction(fmodel,pinstance)
	print "  Test lifted CROI compliance to CROM"
	assert qinstance.compliant(fmodel)
	print "  Test lifted CROI validity to Constraint Model"
	assert fcm.validity(fmodel,qinstance)
	print 
	return None
	
NT=["SD","C","P","S"]
RT=["FD","AP","A","FBS","Sensor","Actuator"]
CT=["FA","R"]
RST=["detectors","announcers","feedback"]
fills=[("SD","R","Sensor"),("C","R","Sensor"),("P","R","Actuator"),("S","R","Actuator"),("SD","FA","FD"),("SD","FA","FBS"),("C","FA","FD"),("P","FA","A"),("S","FA","A"),("R","FA","AP")]
rel={("detectors","FA"): ("FD","AP"),("announcers","FA"): ("AP","A"),("feedback","FA"): ("AP","FBS")}

fmodel=CROM(NT,RT,CT,RST,fills,rel)

print "Test CROM wellformedness..."
assert fmodel.wellformed()

rolec={"R": [((0,inf),"Sensor"),((0,inf),"Actuator")],"FA": [((1,inf),"FD"),((1,inf),"AP"),((1,inf),"A"),((0,inf),"FBS")]}
card={("detectors","FA"): ((1,inf),(1,1)),("announcers","FA"): ((1,1),(1,inf)),("feedback","FA"): ((1,1),(0,inf))}
intra=[]
implication="-|>"
exclusion=">-<"
inter={}
grolec=[]
fcm=ConstraintModel(rolec,card,intra,inter,grolec)
print "Test constraint model compliance..."
assert fcm.compliant(fmodel)

ns=["sd1","c1","c2","s1","p1","p2"]
rs=["r1.s1", "r1.s2", "r1.s3", "r1.a1", "r1.a2", "r1.a3", "fa1.fd1", "fa1.fd2", "fa1.ap1", "fa1.a1", "fa1.a2", "fa1.fbs1"]
cs=["r1", "r2", "fa1"]
type1={"sd1": "SD",  "c1": "C","c2": "C", "s1": "S", "p1": "P", "p2": "P", \
"r1.s1":"Sensor", "r1.s2": "Sensor", "r1.s3": "Sensor", "r1.a1": \
"Actuator", "r1.a2": "Actuator", "r1.a3": "Actuator", \
"fa1.fd1": "FD", "fa1.fd2": "FD", "fa1.ap1": "AP", "fa1.a1": "A", "fa1.a2": "A", "fa1.fbs1": "FBS", \
"r1": "R", "r2": "R", "fa1": "FA"}
plays=[ ("sd1","r1","r1.s1"), ("c1","r1","r1.s2"), ("c2","r1","r1.s3"), \
("s1","r1","r1.a1"), ("p1","r1","r1.a2"), ("p2","r1","r1.a3"), \
("sd1","fa1","fa1.fd1"), ("c1","fa1","fa1.fd2"),  ("r1","fa1","fa1.ap1"), \
("s1","fa1","fa1.a1"), ("p1","fa1","fa1.a2"),  ("sd1","fa1","fa1.fbs1") ]
links={ ("detectors","fa1"): set( [ ("fa1.fd1","fa1.ap1"), ("fa1.fd2","fa1.ap1") ] ), \
("announcers","fa1"): set( [("fa1.ap1","fa1.a1"), ("fa1.ap1","fa1.a2")] ), \
("feedback","fa1"): set( [("fa1.ap1","fa1.fbs1")] ) }
finstance=CROI(ns,rs,cs,type1,plays,links)

print "Test CROI compliance"
assert finstance.compliant(fmodel)
print "Test CROI validity"
assert fcm.validity(fmodel,finstance)

print "Test Persistency Transformations"

print set(itertools.product(fmodel.nt,fmodel.rt,fmodel.ct,set(fmodel.rel.iterkeys())))

pannotations=[ PersistenceAnnotation(fmodel,[],[],["FA"],[]), \
PersistenceAnnotation(fmodel,[],[],["R"],[]), \
PersistenceAnnotation(fmodel,["P"],[],[],[]), \
PersistenceAnnotation(fmodel,[],[],[],[("feedback","FA")]), \
PersistenceAnnotation(fmodel,[],["AP"],[],[]) ]

for pannotation in pannotations:
	testtheorems(pannotation,fmodel,fcm)
	
for nt,rt,ct,rel in set(itertools.product(fmodel.nt,fmodel.rt,fmodel.ct,set(fmodel.rel.iterkeys()))):
	pannotation=PersistenceAnnotation(fmodel,[nt],[rt],[ct],[rel])
	testtheorems(pannotation,fmodel,fcm)

print "All Tests passed successfully"
