#!/usr/bin/env python
# -*- coding: UTF-8 -*-

import itertools

"""crom.py: Proof of concept implementation of the formal role-based modeling language CROM."""

__author__ = "Thomas Kühn"
__copyright__ = "Copyright 2014"
__license__ = "MIT"
__version__ = "1.0.3"

# Basic Defintions

def mutual_disjoint(sets):
	a = set()
	for s in sets:
		for x in s:
			if x in a: return False
			a.add(x)
	return True

def total_function(domain, foo):
	d=frozenset(domain)
	f=set(iter(foo))
	return d <= f


def transitive_closure(a):
	c = set(a)
	while True:
		n = set((x,z) for x,y in c for q,z in c if q == y)
		cn = c | n
		if cn == c:
			break
		c = cn
	return c

# Defintion of Compartment Role Object Models

class CROM:
	'''
	Class representation of a Compartment Role Object Model (CROM).
	'''
  
	def __init__(self,nt,rt,ct,rst,fills,rel):
		'''
		Creates a new CROM instances from the sets of naturel types, role types, compartment types, relationship types, fulfillments, and relationship mappings.
		'''
		self.nt=frozenset(nt)
		self.rt=frozenset(rt)
		self.ct=frozenset(ct)
		self.rst=frozenset(rst)
		self.fills=frozenset(fills)
		self.rel=dict(rel)
		assert mutual_disjoint([self.nt,self.rt,self.ct,self.rst])
		assert self.fills <= set(itertools.product((self.nt | self.ct),self.ct,self.rt))
		assert set(self.rel.iterkeys()) <= set(itertools.product(self.rst,self.ct))
		assert set(self.rel.itervalues()) <= set(itertools.product(self.rt,self.rt))
		
	def __str__(self):
		'''
		Returns a String representation of the CROM.
		'''
		return 'CROM({0},{1},{2},{3},{4},{5})'.format(self.nt,self.rt,self.ct,self.rst,self.fills,self.rel)
		
	def wellformed(self):
		'''
		Returns true iff CROM is well-formed. 
		'''
		return self.axiom1() and self.axiom2() and self.axiom3() and \
		self.axiom4() and self.axiom5()
		
	def axiom1(crom):
		'''
		\\forall rt \\in RT \\exists! ct \\in CT \\exists t \\in (NT \\cup CT) : (t,ct,rt) \\in \\text{fills}
		'''
		return all( len( set([ ct for ct in crom.ct for t in (crom.nt | crom.ct) if (t,ct,rt) in crom.fills ]) )==1 for rt in crom.rt)
		
	def axiom2(crom):
		'''
		\\forall ct \\in CT \\exists (t,ct,rt) \\in \\text{fills}
		'''
		return all( any( f[1]==ct for f in crom.fills )  for ct in crom.ct ) 
		
	def axiom3(crom):
		'''
		\\forall rst \\in RST \\exists ct \\in CT : (rst,ct) \\in \\textbf{domain}(rel)
		'''
		return all( any( (rst,ct) in crom.rel.keys() for ct in crom.ct ) for rst in crom.rst ) 
		
	def axiom4(crom):
		'''
		\\forall (rt_1,rt_2) \\in \\mathbf{codomain}(\\text{rel})\\!: rt_1 \\neq rt_2
		'''
		return all( rt_1 != rt_2 for (rt_1,rt_2) in crom.rel.values() ) 
		
	def axiom5(crom):
		'''
		\\forall (rst,ct) \\in \\mathbf{domain}(\\text{rel}) :
		\\text{rel}(rst,ct) = (rt_1,rt_2)\\ \\wedge (\\_,ct,rt_1),(\\_,ct,rt_2) \\in \\text{fills}
		'''
		return all( any( (t,ct,rt) in crom.fills for t in (crom.nt|crom.ct) ) \
		for (rst,ct) in crom.rel.keys() for rt in crom.rel[(rst,ct)] ) 
		
	def parts(self,ct):
		return set( rt for (t,ct_1,rt) in self.fills if ct_1==ct )

class CROI:
	'''
	Class representation of the Compartment Role Object Instance (CROI).
	'''

	def __init__(self,n,r,c,type1,plays,links):
		'''
		Creates a new CROI from the given sets of naturals, roles, compartments;
		the type mapping; the plays-relation; and links-function.
		'''
		self.n=set(n)
		self.r=set(r)
		self.c=set(c)
		self.type1=dict(type1)
		self.plays=set(plays)
		self.links=dict(links)
		assert mutual_disjoint([self.n,self.r,self.c])
		assert total_function(self.n | self.r | self.c,self.type1)
		assert self.plays <= set(itertools.product((self.n | self.c),self.c,self.r))
		# assert set(self.links.keys()) <= set(itertools.product(self.rst,self.c)) # rst unavailable
		# assert set(self.links.values()) <= set(powerset(itertools.product(self.r,self.r))) #  powerset not scalable
		
	def __str__(self):
		'''
		Returns a String representation of the CROI.
		'''
		return "CROI({0},{1},{2},{3},{4},{5})".format(self.n,self.r,self.c,self.type1,self.plays,self.links)
		
	def compliant(self,crom):
		'''
		Returns true iff the CROI is compliant to the given CROM.
		'''
		return crom.wellformed() and self.axiom6(crom) and self.axiom7(crom) and \
		self.axiom8(crom) and self.axiom9(crom)
		
	def axiom6(croi,crom):
		'''
		\\forall (o,c,r) \\in \\text{plays} : (\\text{type}(o),\\text{type}(c),\\text{type}(r)) \\in \\text{fills}
		'''
		return all( (croi.type1[o],croi.type1[c],croi.type1[r]) in crom.fills for o,c,r in croi.plays)
		
	def axiom7(croi,crom):
		'''
		\forall (o,c,r), (o,c,r') \\in \\text{plays} :
		r \\neq r' \\Rightarrow \\text{type}(r) \\neq \\text{type}(r')
		'''
		return all(croi.type1[r_1]!=croi.type1[r] for o_1,c_1,r_1 in croi.plays for o,c,r in croi.plays if o_1==o and c_1==c and r_1!=r)
		
	def axiom8(croi,crom):
		'''
		\\forall r \in R \\exists ! o \\in O \\exists ! c \\in C : (o,c,r) \\in \\text{plays}
		'''
		return all( len(set([(o,c) for o,c,r_1 in croi.plays if r_1==r]))==1 for r in croi.r )
		
	def axiom9(croi,crom):
		'''
		\\forall rst \\in RST \\forall c \in C \\forall (r_1,r_2) \\in \\text{links}(rst,c) :
		(rst,\\text{type}(c)) \\in \\mathbf{domain} \\wedge
		(_,c,r_1), (_,c,r_2) \\in \\text{plays} \\wedge
		\\text{rel}(rst,\\text{type}(c))=(\\text{type}(r_1),\\text{type}(r_2))
		'''
		return all( (rst,croi.type1[c]) in crom.rel.keys() and \
		crom.rel[(rst,croi.type1[c])] == (croi.type1[r_1],croi.type1[r_2]) and \
		any( (o,c,r_1) in croi.plays for o in croi.o() ) and \
		any( (o,c,r_2) in croi.plays for o in croi.o() )
		for rst in crom.rst for c in croi.c if (rst,croi.type1[c]) in croi.links \
		for (r_1,r_2) in croi.links[(rst,croi.type1[c])] )
	
	def o(self):
		'''
		Returns the union of the natural and compartment instances.
		'''
		return self.n | self.c
		
	def C_ct(self,ct):
		'''
		Returns the compartments instances of the given type
		'''
		return set(c for c in self.c if self.type1[c]==ct)
		
	def o_c(self,c):
		'''
		O^c \\coloneqq \\{ o \\in O \\mid \\exists r \\in R : (o,c,r) \\in \\text{plays} \\}
		'''
		return [ o for o,c_1,r in self.plays if c_1==c ]
		
	def o_c_rt(self,c,rt):
		'''
		O^c_{rt} \\coloneqq \\{ o \\in O \\mid \\exists r \\in R : (o,c,r) \\in \\text{plays} \wedge \\text{type}(r)=rt \\}
		'''
		return [ o for o,c_1,r in self.plays if c_1==c and self.type1[r]==rt ]
	
	def r_c_rt(self,c,rt):
		'''
		R^c_{rt} \\coloneqq \\{ r \\in R \\mid (o,c,r) \\in \\text{plays} \wedge \\text{type}(r)=rt \\}
		'''
		return [ r for o,c_1,r in self.plays if c_1==c and self.type1[r]==rt ]
		
	def pred(self,rst,c,r):
		'''
		\\text{pred}(rst,c,r) \\coloneqq & \\{ r' \\mid (r',r) \\in \\text{links}(\\text{rst},c) \\}
		'''
		if (rst,c) in self.links:
			return [ r_1 for r_1,r_2 in self.links[(rst,c)] if r_2 == r ]
		else:
			return []

	def succ(self,rst,c,r):
		'''
		\\text{succ}(rst,c,r) \\coloneqq & \\{ r' \\mid (r,r') \\in \\text{links}(\\text{rst},c) \\}
		'''
		if (rst,c) in self.links:
			return [ r_2 for r_1,r_2 in self.links[(rst,c)] if r_1 == r ]
		else:
			return []
		
	def player(croi,r):
		'''
		Returns the player of a given role or None if None is given.
		'''
		for o,c,r_1 in croi.plays:
			if r_1==r:
				return o
		raise ValueError("The given role is not played in the croi")
	
	def overline_links(croi,rst,c):
		'''
		\\overline{\\text{links}(rst,c)} \\coloneqq & \\{ (\\overline{r_1},\\overline{r_1}) \\mid (r_1,r_2) \\in \\text{links}(rst,c) \\}
		'''
		return set( (croi.player(r_1),croi.player(r_2)) for r_1,r_2 in croi.links[(rst,c)] )

# Defintion of Role Group


class RoleGroup:
	'''
	Class representation of Role Groups.
	'''

	def __init__(self,rolegroups,lower,upper):
		'''
		Creates a new RoleGroup from the given set as well as the lower and upper bound.
		'''
		self.rolegroups = frozenset(rolegroups)
		self.lower = int(lower)
		self.upper = int(upper)
		if not (0 <= lower <= upper):
			raise ValueError("lower must be less or equal to upper")
			
	def __str__(self):
		'''
		Returns a String representation of the RoleGroup.
		'''
		return "RoleGroup({0},{1},{2})".format(self.rolegroups,self.lower,self.upper)
		
def atoms(a):
	'''
	Recursively, collects the role types (leaf nodes) contained in the given RoleGroup.
	'''
	if isinstance(a,RoleGroup):
		return reduce(set.union, map(atoms, a.rolegroups),set())
	else:
		return set([a])

# Semantics of Role Groups

def evaluate(a,croi,o,c):
	'''
	a^{\\I^c_o} \\coloneqq
  \\begin{cases}
	1 & \\text{\\textbf{if}}\\ a \\in RT \\wedge \\exists (o,c,r) \\in \\text{plays} : type(r)=a
		& \\text{\\textbf{or}} \\quad a \\equiv (B,n,m) \\wedge n \\leq \\sum\\nolimits_{b \\in B}{b^{\\I^c_o}} \\leq m\\\\
	0 & \\text{\\textbf{otherwise}}
	\\end{cases}	
	'''
	if isinstance(a,RoleGroup):
		if (a.lower <= sum( evaluate(b,croi,o,c) for b in a.rolegroups ) <= a.upper):
			return 1
		else:
			return 0
	else:
		if any( (o,c,r) in croi.plays for r in croi.r if croi.type1[r]==a ):
			return 1
		else:
			return 0


class QuantifiedRoleGroup:
	'''
	Class representation of Role Groups.
	'''
	def __init(self):
		pass
		
class QuantifiedGroup(QuantifiedRoleGroup):
	def __init__(self,qrgs,lower,upper):
		'''
		Creates a new QuantifiedRoleGroup from the given set as well as the lower and upper bound.
		'''
		super(QuantifiedGroup, self).__init__()
		self.qrgs = frozenset(qrgs)
		self.lower = int(lower)
		self.upper = int(upper)
		if not (0 <= lower <= upper):
			raise ValueError("lower must be less or equal to upper")
			
	def __str__(self):
		'''
		Returns a String representation of the RoleGroup.
		'''
		return "QuantifiedGroup({0},{1},{2})".format(self.rolegroups,self.lower,self.upper)
		
		
class Quantification(QuantifiedRoleGroup):
	def __init__(self,ct,lower,upper,rolegroup):
		'''
		Creates a new QuantifiedRoleGroup from the given set as well as the lower and upper bound.
		'''
		super(Quantification, self).__init__()
		self.ct=ct
		self.lower = int(lower)
		self.upper = int(upper)
		self.rolegroup = RoleGroup(rolegroup.rolegroups,rolegroup.lower,rolegroup.upper)
		if not (0 <= lower <= upper):
			raise ValueError("lower must be less or equal to upper")
			
	def __str__(self):
		'''
		Returns a String representation of the RoleGroup.
		'''
		return "Quantification({0},{1},{2},{3})".format(self.ct,self.lower,self.upper,self.rolegroup)
			
def unbound(crom,a):
	'''
	Recursively, collects the role types not contained in the quantified compartment types.
	'''
	if isinstance(a,QuantifiedGroup):
	  return set([ unbound(crom,b) for b in a.qrgs])
	elif isinstance(a,Quantification):
	  return atoms(a) - crom.parts(ct)
	else:
		raise ValueError("Given object was neither a QuantifiedGroup nor a Quantification: "+string(a))

# Semantics of Quantified Role Groups

def evaluateQ(a,croi,o):
	'''
	a^{\\I^c_o} \\coloneqq
  \\begin{cases}
	1 & \\text{\\textbf{if}}\\ a \\equiv Q(ct,n,m).b \\wedge n \\leq \\sum\\nolimits_{c \\in C_{ct}}{b^{\\I^c_o}} \\leq m
		& \\text{\\textbf{or}} \\quad a \\equiv (B,n,m) \\wedge n \\leq \\sum\\nolimits_{b \\in B}{b^{\\I_o}} \\leq m\\\\
	0 & \\text{\\textbf{otherwise}}
	\\end{cases}	
	'''
	if isinstance(a,QuantifiedGroup):
		if (a.lower <= sum( evaluateQ(b,croi,o) for b in a.rolegroups ) <= a.upper):
			return 1
		else:
			return 0
	elif isinstance(a,Quantification):
		if (a.lower <= sum( evaluate(a.rolegroup,croi,o,c) for c in croi.C_ct(a.ct) ) <= a.upper):
			return 1
		else:
			return 0		
	else:
		raise ValueError("Given object was neither a QuantifiedGroup nor a Quantification: "+string(a))	

#Definition of standard intra relationship constraints
irreflexive=lambda a,b,r: not(any( x==y for x,y in r))
reflexive=lambda a,b,r: all( (x,x) in r for x in (a|b) )
acyclic=lambda a,b,r: not(any( x==y for x,y in transitive_closure(r) ))
cyclic=lambda a,b,r: all( (x,x) in r for x,y in transitive_closure(r) )
total=lambda a,b,r: all( x==y or (x,y) in r or (y,x) in r for x in (a|b) for y in (a|b) )

# Definition of the positive infinite
inf=float("inf")
# Definition of inter-relationship constraints
implication="-|>"
exclusion=">-<"

class ConstraintModel:
	'''
  Class representation of the Constraint Model.		
	'''
	def __init__(self,rolec,card,intra,inter,grolec):
		'''
		Creates a new ConstraintModel from the given role constraint and cardinality mappings as well as from the set of intra-relationship constraints.
		'''
		self.rolec=dict(rolec)
		self.card=dict(card)
		self.intra=frozenset(intra)
		self.inter=frozenset(inter)
		self.grolec=frozenset(grolec)
		
	def __str__(self):
		'''
		Returns a String representation of the ConstraintModel.
		'''
		return "ConstraintModel({0},{1},{2},{3},{4})".format(self.rolec,self.card,self.intra,self.inter,self.grolec)

	def compliant(self,crom):
		'''
		Returns true iff the ConstraintModel is compliant to the given CROM.
		'''
		return crom.wellformed() and self.axiom10(crom) and \
		self.axiom11(crom) and self.axiom12(crom) and self.axiom13(crom)
		#and self.axiom14(crom)
		
	def axiom10(cm,crom):
		'''
		\\forall ct \\in \textbf{domain}(rolec) \\forall (c,a) \\in \\text{rolec}(ct) :
		\\text{atoms}(a) \\subseteq \\text{parts}(ct)
		'''
		return all( atoms(a) <= crom.parts(ct) for ct in cm.rolec.keys() for crd,a in cm.rolec[ct] )

	def axiom11(cm,crom):
		'''
		\\mathbf{domain}(card) \\subseteq \\mathbf{domain}(rel)
		'''
		return set(cm.card.keys()) <= set(crom.rel.keys())
		
	def axiom12(cm,crom):
		'''
				\\forall (rst,ct,_) \\in \\text{intra} : (rst,ct) \\in \\mathbf{domain}(rel) 
		'''
		return all( (rst,ct) in crom.rel.keys() for (rst,ct,e) in cm.intra )

	def axiom13(cm,crom):
		'''
		\\forall (rst_1,ct,_,rst_2) \in \\text{inter} : rst_1 \\neq rst_2
		(rst_1,ct),(rst_2,ct) \\in \\mathbf{domain}(rel) 
		'''
		return all( rst1 != rst2 and \
		(rst1,ct) in crom.rel.keys() and (rst2,ct) in crom.rel.keys() \
		for (rst1,ct,e,rst2) in cm.inter )

	def oldaxiom14(cm,crom):
		'''
		\\forall a \\in \\ţext{grolec} : unbound(a) = \\emptyset
		'''
		return all( len(unbound(crom,a))==1 for a in cm.grolec ) 
	
	def validity(self,crom,croi):
		'''
		Returns true iff the ConstraintModel is compliant to the given CROM and the given CROI is valid wrt. the ConstraintModel
		'''
		return self.compliant(crom) and croi.compliant(crom) and self.axiom14(crom,croi) and \
		self.axiom15(crom,croi) and self.axiom16(crom,croi) and self.axiom17(crom,croi) and \
		self.axiom18(crom,croi) and self.axiom19(crom,croi) and self.axiom20(crom,croi) 

	def axiom14(cm,crom,croi):
		'''
		\\forall ct \\in CT \\forall (i..j,a) \\in \\text{rolec}(ct) \\forall c \\in C_{ct} :
		i \\leq \\big(\\sum\\nolimits_{o \\in O^c}{a^{\\I^c_o}}\\big) \\leq j
		'''
		return all( \
		crd[0] <= sum( [evaluate(a,croi,o,c) for o in croi.o_c(c)] ) <= crd[1] \
		for ct in crom.ct if ct in cm.rolec	for crd,a in cm.rolec[ct] for c in croi.C_ct(ct) )
		
	def axiom15(cm,crom,croi):
		'''
		\\forall (o,c,r) \\in \\text{plays} \\forall(crd,a) \\in \\text{rolec}(\\text{type}(c)) :
		\\text{type}(r) \\in \\text{atoms}(a) \\Rightarrow a^{\\I^c_o} = 1
		'''
		return all( evaluate(a,croi,o,c)==1 for o,c,r in croi.plays if croi.type1[c] in cm.rolec for crd,a in cm.rolec[croi.type1[c]] if croi.type1[r] in atoms(a) )
		
	def axiom16(cm,crom,croi):
		'''
		\\forall c \\in C \\forall (rst,type(c)) \\in \mathbf{domain}(card) :
		\\text{rel}(rst,type(c))=(rt_1,rt_2) \\wedge
		\\text{card}(rst,type(c))=(i..j,k..l) \\wedge
		\\big( \\forall r_2 \\in R^c_{rt_2}: i \\leq \\big| \\text{pred}(rst,c,r_2) \\big| \\leq j \\big) \\wedge
		\\big( \\forall r_1 \\in R^c_{rt_1}: k \\leq \\big| \\text{succ}(rst,c,r_1) \\big| \\leq l \\big)		
		'''
		return all( \
		all( cm.card[(rst,ct)][0][0] <= len( croi.pred(rst,c,r_2) ) <= cm.card[(rst,ct)][0][1] \
		for r_2 in croi.r_c_rt(c,crom.rel[(rst,ct)][1]) ) and \
		all( cm.card[(rst,ct)][1][0] <= len( croi.succ(rst,c,r_1) ) <= cm.card[(rst,ct)][1][1] \
		for r_1 in croi.r_c_rt(c,crom.rel[(rst,ct)][0]) ) \
		for c in croi.c for (rst,ct) in cm.card.keys() if ct==croi.type1[c] )

	def axiom17(cm,crom,croi):
		'''
		\\forall c \\in C \\forall (rst,type(c),f) \\in intra: \\text{rel}(rst,\\text{type}(c))=(rt_1,rt_2) \wedge f(O^c_{rt_1}, O^c_{rt_1}), \\overline{\\text{links}(rst,c)})=1
		'''
		return all( f(set( croi.o_c_rt(c,crom.rel[ (rst,croi.type1[c]) ][0]) ), \
		set( croi.o_c_rt(c,crom.rel[ (rst,croi.type1[c]) ][1]) ), \
		croi.overline_links(rst,c) )==1 \
		for c in croi.c for (rst,ct,f) in cm.intra if ct==croi.type1[c] and (rst,c) in croi.links)
		
	def axiom18(cm,crom,croi):
		'''
		\\forall c \in C &\ \\forall (rst_1,ct,\otimes,rst_2) \in inter\!:  \\overline{\\text{links}(rst_1,c)} \\cap \\overline{\\text{links}(rst_2,c)} = \emptyset
		'''
		return all( len(croi.overline_links(rst1,c) & croi.overline_links(rst2,c))==0 for c in croi.c for rst1,ct,e,rst2 in cm.inter if ct==croi.type1[c] and e==">-<")
		
	def axiom19(cm,crom,croi):
		'''
		\\forall c \in C &\ \\forall (rst_1,ct,\\trianglelefteq,rst_2) \in inter\!: \\overline{\\text{links}(rst_1,c)} \\subseteq \\overline{\\text{links}(rst_2,c)}
		'''
		return all( croi.overline_links(rst1,c) <= croi.overline_links(rst2,c) for c in croi.c for rst1,ct,i,rst2 in cm.inter if ct==croi.type1[c] and i=="-|>")
		
	def axiom20(cm,crom,croi):
		'''
		\\forall o \in O \\forall a \in grolec: a^{\I_o} = 1
		'''
		return all( evaluateQ(a,croi,o)==1 for o in croi.o() for a in cm.grolec )
