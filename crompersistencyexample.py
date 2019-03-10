#!/usr/bin/env python
# -*- coding: UTF-8 -*-

"""crompersistencyexample.py: Contains the fire alarm example provided in the paper."""

__author__ = "Thomas Kühn"
__copyright__ = "Copyright 2014"
__license__ = "MIT"
__version__ = "1.0.3"

from crom import *
from crompersistency import *

print "=== Example Fire Alarm Model ==="

NT=["SD","C","P","S"]
RT=["FD","AP","A","FBS","Sensor","Actuator"]
CT=["FA","R"]
RST=["detectors","announcers","feedback"]
fills=[("SD","R","Sensor"),("C","R","Sensor"),("P","R","Actuator"),("S","R","Actuator"),("SD","FA","FD"),("SD","FA","FBS"),("C","FA","FD"),("P","FA","A"),("S","FA","A"),("R","FA","AP")]
rel={("detectors","FA"): ("FD","AP"),("announcers","FA"): ("AP","A"),("feedback","FA"): ("AP","FBS")}

fmodel=CROM(NT,RT,CT,RST,fills,rel)

          
print fmodel
if fmodel.wellformed():
	print " The model is a wellformed CROM"
else:
	print " The model is not wellformed"
print

print "=== Example Fire Alarm Constraint Model ==="

rolec={"R": [((0,inf),"Sensor"),((0,inf),"Actuator")],"FA": [((1,inf),"FD"),((1,inf),"AP"),((1,inf),"A"),((0,inf),"FBS")]}
card={("detectors","FA"): ((1,inf),(1,1)),("announcers","FA"): ((1,1),(1,inf)),("feedback","FA"): ((1,1),(0,inf))}
intra=[]
implication="-|>"
exclusion=">-<"
inter={}
grolec=[]

fcm=ConstraintModel(rolec,card,intra,inter,grolec)

print fcm
if fcm.compliant(fmodel):
	print " The constraint model is compliant to the CROM"
else:
	print " The constraint model is not compliant to the CROM"

print

print "=== Example Fire Alarm Instance ==="

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
print plays
print (set(plays) - set(itertools.product((set(ns) | set(cs)),set(cs),set(rs))))
finstance=CROI(ns,rs,cs,type1,plays,links)

print finstance
if finstance.compliant(fmodel):
	print " The CROI is compliant to the CROM"
else:
	print " The CROI is not compliant to the CROM"
if fcm.validity(fmodel,finstance):
	print " The CROI is valid to the Constraint Model wrt. CROM"
else:
	print " The CROI is invalid to the Constraint Model wrt. CROM"
print


print "=== Persistency Transformation ==="

#pannotation=PersistenceAnnotation(fmodel,[],[],["FA"],[])
pannotation=PersistenceAnnotation(fmodel,[],[],["R"],[])
#pannotation=PersistenceAnnotation(fmodel,["P"],[],[],[])
#pannotation=PersistenceAnnotation(fmodel,[],[],[],[("feedback","FA")])
#pannotation=PersistenceAnnotation(fmodel,[],["AP"],[],[])
print pannotation

ext=compute_ext(fmodel,fcm)
print ext

pfills=pannotation.compute_fills(fmodel,fcm,ext)
print "fills:"
print fmodel.fills
print "persisted fills:"
print pfills

prel=pannotation.compute_rel(fmodel,fcm,pfills)
print "rel:"
print fmodel.rel
print "persited rel:"
print prel


poccur=pannotation.compute_occur(fcm,pfills,prel)
print "occur:"
print fcm.rolec
print "persited occur:"
print poccur

pcard=pannotation.compute_card(fcm,pfills,prel)
print "card:"
print fcm.card
print "persited card:"
print pcard

print "=== Persisted Model and Constraint Model==="

pmodel,pcm = transformation(fmodel,fcm,pannotation)

print pmodel
if pmodel.wellformed():
	print " The persisted model is a wellformed CROM"
else:
	print " The persisted model is not wellformed"

print


print pcm
if pcm.compliant(pmodel):
	print " The persisted constraint model is compliant to the persisted CROM"
else:
	print " The persisted constraint model is not compliant to the persisted CROM"

print

print "CROI restriction:"
pinstance=restriction(pmodel,finstance)
print pinstance
if pinstance.compliant(pmodel):
	print " The persited CROI is compliant to the persisted CROM"
else:
	print " The persited CROI is not compliant to the persited CROM"
if pcm.validity(pmodel,pinstance):
	print " The persited CROI is valid to the persited Constraint Model wrt. persited CROM"
else:
	print " The persited CROI is invalid to the persited Constraint Model wrt. persited CROM"
print

print "CROI lifting:"
qinstance=restriction(fmodel,pinstance)
print qinstance
if qinstance.compliant(fmodel):
	print " The lifted CROI is compliant to the CROM"
else:
	print " The lifted CROI is not compliant to the CROM"
if fcm.validity(fmodel,qinstance):
	print " The lifted CROI is valid to the Constraint Model wrt. CROM"
else:
	print " The lifted CROI is invalid to the Constraint Model wrt. CROM"
print

