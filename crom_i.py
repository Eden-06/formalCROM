#!/usr/bin/env python
# -*- coding: UTF-8 -*-



"""crom_i.py: Proof of concept implementation of the formal role-based modeling language CROM with Inheritance."""

__author__ = "Thomas Kühn"
__copyright__ = "Copyright 2014"
__license__ = "MIT"
__version__ = "1.0.0"
__metaclass__ = type

from crom import *

# Defintion of Compartment Role Object Models with Inheritance

class CROM_I(CROM):
	'''
	Class representation of a Compartment Role Object Model with Inheritance (CROM\textsubscript{I}).
	\\mathcal{N}=(NT, RT, CT, RST, F, M, \\text{fills}, \\text{rel}, \\prec_{NT}, \\prec_{CT} )
	'''
  
	def __init__(self,nt,rt,ct,rst,fills,rel,prec_nt,prec_ct):
		'''
		Creates a new CROM with Inheritance instances from the sets of
		naturel types, role types, compartment types, relationship types, 
		fulfillments	as well as relationship mappings.
		Moreover, \prec_{NT} and \prec_{CT} denote the inheritance relation
		between natural types and role types.
		'''
		super(CROM_I, self).__init__(nt,rt,ct,rst,fills,rel)
		self.prec_nt=frozenset(prec_nt)		
		self.prec_ct=frozenset(prec_ct)
		assert self.prec_nt <= set(itertools.product(self.nt,self.nt))
		assert self.prec_ct <= set(itertools.product(self.ct,self.ct))
		
	def __str__(self):
		'''
		Returns a String representation of the CROM.
		'''
		return 'CROM_I({0},{1},{2},{3},{4},{5},{6},{7})'.format(self.nt,self.rt,self.ct,self.rst,self.fills,self.rel,self.prec_nt,self.prec_ct)
	
	def preceq_nt(self):
		'''
		Reflexive transitive closure over the natural inheritance relation prec_nt.
		'''
		return transitive_closure(self.prec_nt) | set([(nt,nt) for nt in self.nt])
	
	def preceq_ct(self):
		'''
		Reflexive Transitive closure over the compartment inheritance relation prec_ct.
		'''
		return transitive_closure(self.prec_ct) | set([(ct,ct) for ct in self.ct])

	def preceq_t(self):
		'''
		Reflexive transitive closure over the natural and the compartment inheritance relation.
		'''
		return self.preceq_nt() | self.preceq_ct()
	
	def wellformed(self):
		'''
		Returns true iff CROM is well-formed. 
		'''
		return self.axiom1() and self.axiom2() and \
		self.axiom3() and self.axiom4() and self.axiom5() and \
		self.axiom6() and self.axiom7() and self.axiom8()
		
	def axiom1(crom):
		'''
		\\forall rt \\in RT \\exists ct \\in CT \\exists t \\in (NT \\cup CT) : (t,ct,rt) \\in \\text{fills}
		'''
		return all( any( (t,ct,rt) in crom.fills for t in (crom.nt | crom.ct) for ct in crom.ct) for rt in crom.rt)
		
	def axiom6(crom):
		'''
		\\forall (ct_1,ct_2) \\in \\preceq_{CT} \\text{parts}(ct_2) \\subseteq \\text{parts}(ct_1)
		'''
		return all( crom.parts(ct_2) <= crom.parts(ct_1) for (ct_1,ct_2) in crom.preceq_ct() )
	
	def axiom7(crom):
		'''
		\\forall (ct_1,ct_2) \\in \\preceq_{CT} \\forall (rst,ct_2) \\in \\mathbf{domain}(\\text{rel}):
		(rst,ct_1) \\in \\mathbf{domain}(\\text{rel}) \\wedge \\text{rel}(rst,ct_2)=\\text{rel}(rst,ct_1)
		'''
		return all(  (rst,ct_1) in crom.rel.keys() and crom.rel[(rst,ct_1)]==crom.rel[(rst,ct_2)] \
		for (ct_1,ct_2) in crom.preceq_ct() for (rst,ct) in crom.rel.keys() if ct==ct_2 ) 

	def axiom8(crom):
		'''
		\\forall (ct_1,ct_2) \\in \\preceq_{CT} \\forall rt \\in \\text{parts}(ct_2) 
		\\forall (s,ct_1,rt) \\in \\text{fills} \\exists (t,ct_2,rt) \\in \\text{fills} : s \\preceq_{T} t
		'''
		return all( any( (s,t) in crom.preceq_t() \
		for t,ct,rt_t   in crom.fills if ct==ct_2 and rt_t==rt ) \
		for ct_1,ct_2 in crom.preceq_ct() for rt in crom.parts(ct_2) \
		for s,ct_s,rt_s in crom.fills if rt_s==rt and ct_s==ct_1 ) 


# Defintion of Compartment Role Object Instances

class CROI_I(CROI):
	'''
	Class representation of the Compartment Role Object Instance (CROI).
	'''

	def __init__(self,n,r,c,type1,plays,links):
		'''
		Creates a new CROI from the given sets of naturals, roles, compartments;
		the type mapping; the plays-relation; and links-funktion.
		'''
		super(CROI_I,self).__init__(n,r,c,type1,plays,links)


	def compliant(self,crom):
		'''
		Returns true iff the CROI is compliant to the given CROM.
		'''
		return crom.wellformed() and self.axiom6(crom) and \
		self.axiom7(crom) and self.axiom8(crom) and self.axiom9(crom)
	
	def axiom6(croi,crom):
		'''
		\\forall (o,c,r) \\in \\text{plays} \\exists (t,\\text{type}(c),\\text{type}(r)) \\in \\text{fills}: \\text{type}(o) \\preceq_{T} t
		'''

		for (o,c,r) in croi.plays:
			if not any( (croi.type1[o],t) in crom.preceq_t() for (t,ct,rt) in crom.fills if ct==croi.type1[c] and rt==croi.type1[r] ):
				print "({0}:{1},{2}:{3},{4}:{5}) failed".format(o,croi.type1[o],c,croi.type1[c],r,croi.type1[r])
		return all( any( (croi.type1[o],t) in crom.preceq_t() \
		for (t,ct,rt) in crom.fills if ct==croi.type1[c] and rt==croi.type1[r] ) \
		for (o,c,r) in croi.plays )
	

# Extended Semantics of Quantified Role Groups

def evaluateQ_I(a,crom,croi,o):
	'''
	a^{\\I^c_o} \\coloneqq
  \\begin{cases}
	1 & \\text{\\textbf{if}}\\ a \\equiv Q(ct,n,m).b \\wedge n \\leq \\sum\\nolimits_{c \\in C_{ct}}{b^{\\I^c_o}} \\leq m
		& \\text{\\textbf{or}} \\quad a \\equiv (B,n,m) \\wedge n \\leq \\sum\\nolimits_{b \\in B}{b^{\\I_o}} \\leq m\\\\
	0 & \\text{\\textbf{otherwise}}
	\\end{cases}	
	'''
	if isinstance(a,QuantifiedGroup):
		if (a.lower <= sum( evaluateQ_I(b,crom,croi,o) for b in a.qrgs ) <= a.upper):
			return 1
		else:
			return 0
	elif isinstance(a,Quantification):
		if (a.lower <= sum( evaluate(a.rolegroup,croi,o,c) \
		for (ct_1,ct_2) in crom.preceq_ct() if ct_2==a.ct \
		for c in croi.c if croi.type1[c]==ct_1 ) <= a.upper):
			return 1
		else:
			return 0		
	else:
		raise ValueError("Given object was neither a QuantifiedGroup nor a Quantification: "+string(a))	

class ConstraintModel_I(ConstraintModel):
	'''
  Class representation of the Constraint Model.		
	'''
	def __init__(self,rolec,card,intra,inter,grolec):
		'''
		Creates a new ConstraintModel from the given role constraint and cardinality mappings as well as from the set of intra-relationship constraints.
		'''
		super(ConstraintModel_I,self).__init__(rolec,card,intra,inter,grolec)
		
#	def compliant(self,crom):
#		'''
#		Returns true iff the ConstraintModel is compliant to the given CROM.
#		'''
#		return crom.wellformed() and self.axiom10(crom) and \
#		self.axiom11(crom) and self.axiom12(crom) and self.axiom13(crom)

	def validity(self,crom,croi):
		'''
		Returns true iff the ConstraintModel is compliant to the given CROM and the given CROI is valid wrt. the ConstraintModel
		'''
		return self.compliant(crom) and croi.compliant(crom) and self.axiom14(crom,croi) and \
		self.axiom15(crom,croi) and self.axiom16(crom,croi) and self.axiom17(crom,croi) and \
		self.axiom18(crom,croi) and self.axiom19(crom,croi) and self.axiom20(crom,croi) 

	def axiom14(cm,crom,croi):
		'''
		\\forall c \\in C \\forall (\\text{type}(c),ct) \\in \\preceq_{CT} \\forall (i..j,a) \\in \\text{rolec}(ct) : 
		i \\leq \\Big(\\sum\\nolimits_{o \\in O^c}{a^{\\I^c_o}}\\Big) \\leq j
		'''
		return all( \
		crd[0] <= sum( [evaluate(a,croi,o,c) for o in croi.o_c(c)] ) <= crd[1] \
		for c in croi.c for ct_1,ct in crom.preceq_ct() if ct_1==croi.type1[c] and ct in cm.rolec for crd,a in cm.rolec[ct] )
		
	def axiom15(cm,crom,croi):
		'''
		\\forall (o,c,r) \\in \\text{plays} \\forall (\\text{type}(c),ct) \\in \\preceq_{CT}
		\\forall(crd,a) \\in \\text{rolec}(ct) :
		\\text{type}(r) \\in \\text{atoms}(a) \\Rightarrow a^{\\I^c_o} = 1
		'''
		return all( evaluate(a,croi,o,c)==1 \
		for o,c,r in croi.plays for ct_1,ct in crom.preceq_ct() if ct_1==croi.type1[c] and ct in cm.rolec \
		for crd,a in cm.rolec[croi.type1[c]] if croi.type1[r] in atoms(a) )
		
	def axiom16(cm,crom,croi):
		'''
		\\forall c \\in C \\forall (\\text{type}(c),ct) \\in \\preceq_{CT}
		\\forall (rst,ct) \\in \\mathbf{domain}(card) :
		  \\text{rel}(rst,ct)=(rt_1,rt_2) \\wedge \\text{card}(rst,ct)=(i..j,k..l) \\wedge
		  \\big( \\forall r_2 \\in R^c_{rt_2} : i \\leq \\big| \\text{pred}(rst,c,r_2) \\big| \\leq j \\big) \\wedge
			\\big( \\forall r_1 \\in R^c_{rt_1} : k \\leq \\big| \\text{succ}(rst,c,r_1) \\big| \\leq l \\big)
		'''
		return all( \
		all( cm.card[(rst,ct)][0][0] <= len( croi.pred(rst,c,r_2) ) <= cm.card[(rst,ct)][0][1] \
		for r_2 in croi.r_c_rt(c,crom.rel[(rst,ct)][1]) ) and \
		all( cm.card[(rst,ct)][1][0] <= len( croi.succ(rst,c,r_1) ) <= cm.card[(rst,ct)][1][1] \
		for r_1 in croi.r_c_rt(c,crom.rel[(rst,ct)][0]) ) \
		for c in croi.c for ct_1,ct_2 in crom.preceq_ct() if ct_1==croi.type1[c] \
		for (rst,ct) in cm.card.keys() if ct==ct_2 )

	def axiom17(cm,crom,croi):
		'''
		\\forall c \\in C \\forall (\\text{type}(c),ct) \\in \\preceq_{CT} \\forall (rst,ct,f) \\in intra :
		\\text{rel}(rst,ct)=(rt_1,rt_2) \\wedge f(O^c_{rt_1}, O^c_{rt_2}, \\overline{\\text{links}(rst,c)})=1
		'''
		return all( f(set( croi.o_c_rt(c,crom.rel[ (rst,croi.type1[c]) ][0]) ), \
		set( croi.o_c_rt(c,crom.rel[ (rst,croi.type1[c]) ][1]) ), \
		croi.overline_links(rst,c) )==1 \
		for c in croi.c for ct_1,ct_2 in crom.preceq_ct() if ct_1==croi.type1[c] \
		for (rst,ct,f) in cm.intra if ct==ct_2 and (rst,c) in croi.links)
		
	def axiom18(cm,crom,croi):
		'''
		\\forall c \\in C \\forall (\\text{type}(c),ct) \\in \\preceq_{CT} \\forall (rst_1, ct, \\otimes,rst_2) \\in inter :
		\\overline{\\text{links}(rst_1,c)} \\cap \\overline{\\text{links}(rst_2,c)} = \\emptyset

		'''
		return all( len(croi.overline_links(rst1,c) & croi.overline_links(rst2,c))==0 \
		for c in croi.c for ct_1,ct_2 in crom.preceq_ct() if ct_1==croi.type1[c]  \
		for rst1,ct,e,rst2 in cm.inter if ct==ct_2 and e==">-<" )
		
	def axiom19(cm,crom,croi):
		'''
		\\forall c \\in C \\forall (\\text{type}(c),ct) \\in \\preceq_{CT} \\forall (rst_1, ct, \\trianglelefteq, rst_2) \\in inter :
		\\overline{\\text{links}(rst_1,c)} \\subseteq \\overline{\\text{links}(rst_2,c)}
		'''
		return all( croi.overline_links(rst1,c) <= croi.overline_links(rst2,c) \
		for c in croi.c for ct_1,ct_2 in crom.preceq_ct() if ct_1==croi.type1[c]  \
		for rst1,ct,i,rst2 in cm.inter if ct==ct_2 and i=="-|>")
		
	def axiom20(cm,crom,croi):
		'''
		\\forall o \\in O \\forall \\varphi \\in \\text{grolec} : \\varphi^{\\mathcal{H}_o} = 1 
		'''
		return all( evaluateQ_I(a,crom,croi,o)==1 for o in croi.o() for a in cm.grolec )
