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
		for (rst,ct) in crom.rel.iterkeys():
			if ct in self.ct:
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
	#Rule 36
	plays=set( [(o,c,r) for (o,c,r) in croi.plays \
	if (croi.type1[o],croi.type1[c],croi.type1[r]) in pcrom.fills] )
	#Rule 37
	links=dict()
	for (rst,c) in croi.links.iterkeys():
		ct=croi.type1[c]
		if (rst,ct) in pcrom.rel:  		
			links[(rst,c)]=set( [(r1,r2) for (r1,r2) in croi.links[(rst,c)] \
			if pcrom.rel[(rst,ct)][0]==croi.type1[r1] and pcrom.rel[(rst,ct)][1]==croi.type1[r2] ])
	#construction of the sets
	ns=set( [n for (n,c,r) in plays if croi.type1[n] in pcrom.nt] )
	rs=set( [r for (n,c,r) in plays] )
	cs=set( [n for (n,c,r) in plays if croi.type1[n] in pcrom.ct] ) | set( [c for (n,c,r) in plays] )
	type1=dict(croi.type1)
	#Restricted CROI
	result=CROI(ns,rs,cs,type1,plays,links)
	return result



