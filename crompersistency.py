#!/usr/bin/env python
# -*- coding: UTF-8 -*-

"""crompersistency.py: Contains the transformation algorithm described in the paper."""

__author__ = "Thomas Kühn"
__copyright__ = "Copyright 2019"
__license__ = "MIT"
__version__ = "0.0.1"

from crom import *

class PersistenceAnnotation:
	'''
	Class representation of a persistence annotation for a CROM.
	'''
  
	def __init__(self,crom,nt,rt,ct,rel):
		'''
		Creates a new persistence annotation from the sets of naturel types, role types, compartment types, and relationship mappings.
		'''
		self.nt=frozenset(nt)
		self.rt=frozenset(rt)
		self.ct=frozenset(ct)
		self.rel=frozenset(rel)
		assert self.nt <= crom.nt
		assert self.rt <= crom.rt
		assert self.ct <= crom.ct
		assert self.rel <= set(crom.rel.iterkeys())
		
	def __str__(self):
		'''
		Returns a String representation of the persistence annotation.
		'''
		return 'PersistenceAnnotation({0},{1},{2},{3})'.format(self.nt,self.rt,self.ct,self.rel)
	
	def compute_fills(self,crom,constraintmodel,ext):
		result=set()
		#CTSel
		result.update( [(t,ctp,rt) for ctp in self.ct for (t,ct,rt) in crom.fills if ctp==ct] )
		#RTSel
		result.update( [(t,ct,rtp) for rtp in self.rt for (t,ct,rt) in crom.fills if rtp==rt] )
		#RSTSelLeft
		result.update( [(t,ctp,rt) for (rstp,ctp) in self.rel for (t,ct,rt) in crom.fills if ctp==ct and crom.rel[(rstp,ctp)][0]==rt ] )
		#RSTSelRight
		result.update( [(t,ctp,rt) for (rstp,ctp) in self.rel for (t,ct,rt) in crom.fills if ctp==ct and  crom.rel[(rstp,ctp)][1]==rt ] )
		#inductive cases
		oldsize=-1
		while oldsize<len(result):
			oldsize=len(result)
			#CTExt
			result.update( [ (t,ct1,rt) for (ct1,ct2,_) in result if ct1 in crom.ct \
			for (t,ct,rt) in crom.fills if ct1==ct and rt in ext[ct1] ] )
			#OccurExt
			result.update( [ (t,ct,rt) for (_,ct1,_) in result \
			for (t,ct,rt) in crom.fills if ct1==ct and rt in ext[ct1] ] )
			#RelExtLeft
			result.update( [ (t,ct,rt2) for (s,ct1,rt1) in result \
			for (t,ct,rt2) in crom.fills if ct1==ct \
			for (rst,ct2) in constraintmodel.card.iterkeys() \
			if ct2==ct and crom.rel[(rst,ct)][0]==rt1 and crom.rel[(rst,ct)][1]==rt2 and \
			constraintmodel.card[(rst,ct)][1][0]>=1 ] )
			#RelExtRight
			result.update( [ (s,ct,rt1) for (t,ct1,rt2) in result \
			for (s,ct,rt1) in crom.fills if ct1==ct \
			for (rst,ct2) in constraintmodel.card.iterkeys() \
			if ct2==ct and crom.rel[(rst,ct)][0]==rt1 and crom.rel[(rst,ct)][1]==rt2 and \
			constraintmodel.card[(rst,ct)][0][0]>=1 ] )
		return result
	
	def compute_rel(self,crom,constraintmodel,fills):
		result=dict()
		#RelSel
		for (rst,ct) in self.rel:
			result[(rst,ct)]=crom.rel[(rst,ct)]
		#RelInCT
		for ct in self.ct:
			for (rst,ct) in crom.rel.iterkeys():
				result[(rst,ct)]=crom.rel[(rst,ct)]
		#inductive case
		oldsize=-1
		while oldsize<len(result):
			oldsize=len(result)
			#RelExt
			ext=[ (rst,ct) for (rst,ct) in constraintmodel.card \
			for (s,ct1,rt1) in fills if ct1==ct \
			for (t,ct2,rt2) in fills if ct2==ct and \
			crom.rel[(rst,ct)][0]==rt1 and crom.rel[(rst,ct)][1]==rt2 and \
			(constraintmodel.card[(rst,ct)][0][0]>=1 or constraintmodel.card[(rst,ct)][1][0]>=1) ]
			for (rst,ct) in ext:
				result[(rst,ct)]=crom.rel[(rst,ct)]
		return result
	
	def compute_occur(self,constraintmodel,fills,rel):
		#OccurIn
		result=dict()
		for ct in constraintmodel.rolec.iterkeys():
			p=set( [ (a,rt) for (a,rt) in constraintmodel.rolec[ct] \
			for (t,ct1,rt1) in fills if ct1==ct and rt1==rt ] )
			if len(p)>0:
				result[ct]=p
		return result
	
	def compute_card(self,constraintmodel,fills,rel):
		#CardIn
		result=dict()
		for (rst,ct) in rel.iterkeys():
			if (rst,ct) in constraintmodel.card:			
				result[(rst,ct)]=constraintmodel.card[(rst,ct)]
		return result

def compute_ext(crom,constraintmodel):
	result=dict()
	for ct in crom.ct:
		result[ct]=frozenset( [rt for (c,rt) in constraintmodel.rolec[ct] if c[0]>=1] ) 
	return result	
		
def transformation(crom,constraintmodel,annotation):
	assert crom.wellformed()
	assert constraintmodel.compliant(crom)
	#precompute ext
	ext=compute_ext(crom,constraintmodel)
	#compute fills
	fills=annotation.compute_fills(crom,constraintmodel,ext)
	#compute rel
	rel=annotation.compute_rel(crom,constraintmodel,fills)
	#initialize sets
	ts= set( [t for (t,ct,rt) in fills] )
	cts=set( [ct for (t,ct,rt) in fills] )
	rts=set( [rt for (t,ct,rt) in fills] )
	nts=annotation.nt | (ts - cts)
	rsts=set( [rst for (rst,ct) in rel.iterkeys()] )
	#construction of the model
	pcrom=CROM(nts,rts,cts,rsts,fills,rel)
	#compute occur (cf. rolec)
	occur=annotation.compute_occur(constraintmodel,fills,rel)
	#compute card
	card=annotation.compute_card(constraintmodel,fills,rel)
	pcm=  ConstraintModel(occur,card,[],{},[])
	return (pcrom,pcm)

def restriction(pcrom,croi):
	pass
	result=CROI(ns,rs,cs,type1,plays,links)
	return result



# Example Model for the Bank

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


print "=== Persistency Transformation ==="

pannotation=PersistenceAnnotation(fmodel,[],["AP"],[],{})
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


print

