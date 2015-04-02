#!/usr/bin/env python
# -*- coding: UTF-8 -*-

"""crom.py: Proof of concept implementation of the formal role-based modeling language CROM."""

__author__ = "Thomas Kühn"
__copyright__ = "Copyright 2014"
__license__ = "MIT"
__version__ = "1.0.0"

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

# Defintion of Compartment Role Object Models

class CROM:
	'''
	Class representation of a Compartment Role Object Model (CROM).
	'''
  
	def __init__(self,nt,rt,ct,rst,fills,parts,rel):
		'''
		Creates a new CROM instances from the sets of naturel types,
		role types, compartment types, relationship types, fulfillments,
		as well as from the parts and relationship mappings.
		'''
		self.nt=frozenset(nt)
		self.rt=frozenset(rt)
		self.ct=frozenset(ct)
		self.rst=frozenset(rst)
		self.fills=frozenset(fills)
		self.parts=dict(parts)
		self.rel=dict(rel)
		assert mutual_disjoint([self.nt,self.rt,self.ct,self.rst])
		assert total_function(self.ct,self.parts)
		assert total_function(self.rst,self.rel)
		
	def __str__(self):
		'''
		Returns a String representation of the CROM.
		'''
		return 'CROM({0},{1},{2},{3},{4},{5},{6})'.format(self.nt,self.rt,self.ct,self.rst,self.fills,self.rel,self.parts)
		
	def wellformed(self):
		'''
		Returns true iff CROM is well-formed. 
		'''
		return self.axiom1() and self.axiom2() and self.axiom3() and \
		self.axiom4() and self.axiom5()
		
	def axiom1(crom):
		'''
		\\forall rt \\in RT \\exists t \\in (NT \\cup CT) : (t,rt) \\in \\text{fills}
		'''
		return all( any( (t,rt) in crom.fills for t in (crom.nt | crom.ct) ) for rt in crom.rt)
		
	def axiom2(crom):
		'''
		\\forall ct \in CT : \\text{parts}(ct) \\neq \\emptyset
		'''
		return all( len(crom.parts[ct])>0 for ct in crom.ct ) 
		
	def axiom3(crom):
		'''
		\\forall rt \\in RT \\exists ! ct \\in CT : rt \\in \\text{parts}(ct)
		'''
		return all( len( [True for ct in crom.ct if rt in crom.parts[ct]] )==1 for rt in crom.rt ) 
		
	def axiom4(crom):
		'''
		\\forall rst \\in RST \\text{rel}(rst) = (rt_1,rt_2) \\wedge rt_1 \\neq rt_2
		'''
		return all( crom.rel[rst][0]!=crom.rel[rst][1] for rst in crom.rst )
		
	def axiom5(crom):
		'''
		\\forall rst \\in RST \\exists ct \\in CT : \\text{rel}(rst) = (rt_1,rt_2) \\wedge  rt_1,rt_2 \\in \\text{parts}(ct)
		'''
		return all( any(set(crom.rel[rst]) <= set(crom.parts[ct]) for ct in crom.ct) for rst in crom.rst)

# Defintion of Compartment Role Object Instances


class CROI:
	'''
	Class representation of the Compartment Role Object Instance (CROI).
	'''

	def __init__(self,n,r,c,type1,plays,links):
		'''
		Creates a new CROI from the given sets of naturals, roles, compartments;
		the type mapping; the plays-relation; and links-funktion.
		'''
		self.n=set(n)
		self.r=set(r)
		self.c=set(c)
		self.type1=dict(type1)
		self.plays=set(plays)
		self.links=dict(links)
		assert mutual_disjoint([self.n,self.r,self.c,set([None])])
		assert total_function(self.n | self.r | self.c,self.type1)
		# assert total_function(???,self.links)
		
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
		self.axiom8(crom) and self.axiom9(crom) and self.axiom10(crom) and self.axiom11(crom)
		
	def axiom6(croi,crom):
		'''
		\\forall (o,c,r) \\in \\text{plays} : 
		(\\text{type}(o),\\text{type}(r)) \\in \\text{fills} \\wedge
		\\text{type}(r) \\in \\text{parts}(\\text{type}(c))
		'''
		return all(((croi.type1[o],croi.type1[r]) in crom.fills) and (croi.type1[r] in crom.parts[croi.type1[c]]) for o,c,r in croi.plays)
		
	def axiom7(croi,crom):
		'''
		\forall (o,c,r), (o,c,r') \\in \\text{plays} :
		r \\neq r' \\Rightarrow \\text{type}(r) \\neq \\text{type}(r')
		'''
		return all(croi.type1[r_1]!=croi.type1[r] for o_1,c_1,r_1 in croi.plays for o,c,r in croi.plays if o_1==o and c_1==c and r_1!=r)
		
	def axiom8(croi,crom):
		'''
		\\forall r \in R \\exists ! o \\in O \\exists ! c \\in C : 
		(o,c,r) \\in \\text{plays}
		'''
		return all( len(set([(o,c) for o,c,r_1 in croi.plays if r_1==r]))==1 for r in croi.r )
		
	def axiom9(croi,crom):
		'''
		\\forall rst \\in RST \\forall c \in C :
		(\\varepsilon,\\varepsilon) \\not\\in \\text{links}(rst,c)
		'''
		return all( (None,None) not in croi.links[(rst,c)] for rst in crom.rst for c in croi.c if (rst,c) in croi.links)
		
	def axiom10(croi,crom):
		'''
		\\forall rst \\in RST \\forall c \\in C \\forall r \\in R\\ \\forall o \\in O \\exists \\hat{r} \\in R^{\\varepsilon}:
		\\text{rel}(rst) = (rt_{1},rt_{2})\\ \\wedge
    \\big((o,c,r) \\in \\text{plays} \\land \\text{type}(r)=rt_{1}\\big)
		\\Leftrightarrow \\big( (r,\\hat{r}) \\in \\text{links}(rst,c)\\big)\\ \\wedge
		\\big((o,c,r) \\in \\text{plays} \\land \\text{type}(r)=rt_{2}\\big)
		\\ \\Leftrightarrow \\big( (\\hat{r},r) \\in \\text{links}(rst,c)\\big)
		'''
		return all( any((((o,c,r) in croi.plays and croi.type1[r]==crom.rel[rst][0]) == bool((r,r_1) in croi.links[(rst,c)])) and (((o,c,r) in croi.plays and croi.type1[r]==crom.rel[rst][1]) == bool((r_1,r) in croi.links[(rst,c)]) ) for r_1 in croi.repsilon() ) for rst in crom.rst for c in croi.c if (rst,c) in croi.links for r in croi.r for o in croi.o())

	def axiom11(croi,crom):
		'''
		\\forall rst \\in RST \\forall c \\in C \\forall (r_1,r_2) \\in \\text{links}(rst,c) \\cap R \\times R :
(r_1,\\varepsilon), (\\varepsilon,r_2) \\notin \\text{links}(rst,c)
		'''
		return all(((r_1,None) not in croi.links[(rst,c)]) and ((None,r_2) not in croi.links[(rst,c)]) for rst in crom.rst for c in croi.c if (rst,c) in croi.links for r_1,r_2 in croi.links[(rst,c)] if r_1 != None and r_2 != None)
	
	def o(self):
		'''
		Returns the union of the natural and compartment instances.
		'''
		return self.n | self.c
		
	def o_c(self,c):
		'''
		O^c \\coloneqq \\{ o \\in O \\mid \\exists r \\in R : (o,c,r) \\in \\text{plays} \\}
		'''
		return [ o for o,c_1,r in self.plays if c_1==c ]
		
	def	repsilon(self):
		'''
		Returns the set of roles extended by the None object (\\varepsilon).
		'''
		return self.r | set([None])

	def pred(self,rst,c,r):
		'''
		\\text{pred}(rst,c,r) \\coloneqq & \\{ r' \\mid (r',r) \\in \\text{links}(\\text{rst},c) \\wedge r' \\neq \\varepsilon \\}
		'''
		if (rst,c) in self.links:
			return [ r_1 for r_1,r_2 in self.links[(rst,c)] if r_2 == r ]
		else:
			return []

	def succ(self,rst,c,r):
		'''
		\\text{succ}(rst,c,r) \\coloneqq & \\{ r' \\mid (r,r') \\in \\text{links}(\\text{rst},c) \\wedge r' \\neq \\varepsilon \\}
		'''
		if (rst,c) in self.links:
			return [ r_2 for r_1,r_2 in self.links[(rst,c)] if r_1 == r ]
		else:
			return []
		
	def player(croi,r):
		'''
		Returns the player of a given role or None if None is given.
		'''
		if r==None:
			return None
		for o,c,r_1 in croi.plays:
			if r_1==r:
				return o
		raise ValueError("The given role is not played in the croi")
	
	def overline_links(croi,rst,c):
		'''
		\\overline{\\text{links}(rst,c)} \\coloneqq & \\{ (\\overline{r_1},\\overline{r_1}) \\mid (r_1,r_2) \\in \\text{links}(rst,c) \\}
		'''
		return set([ (croi.player(r_1),croi.player(r_2)) for r_1,r_2 in croi.links[(rst,c)] ])

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

class ConstraintModel:
	'''
  Class representation of the Constraint Model.		
	'''
	def __init__(self,rolec,card,intra):
		'''
		Creates a new ConstraintModel from the given role constraint and cardinality mappings as well as from the set of intra-relationship constraints.
		'''
		self.rolec=dict(rolec)
		self.card=dict(card)
		self.intra=frozenset(intra)
		# assert total function
		
	def __str__(self):
		'''
		Returns a String representation of the ConstraintModel.
		'''
		return "ConstraintModel({0},{1},{2})".format(self.rolec,self.card,self.intra)

	def compliant(self,crom):
		'''
		Returns true iff the ConstraintModel is compliant to the given CROM.
		'''
		return crom.wellformed() and self.axiom12(crom)
		
	def axiom12(cm,crom):
		'''
		\\forall ct \\in CT \\forall (c,a) \\in \\text{rolec}(ct) :
		\\text{atoms}(a) \\subseteq \\text{parts}(ct)
		'''
		return all( atoms(a) <= set(crom.parts[ct]) for ct in crom.ct if ct in cm.rolec for crd,a in cm.rolec[ct] )
		
	def validity(self,crom,croi):
		'''
		Returns true iff the ConstraintModel is compliant to the given CROM and the given CROI is valid wrt. the ConstraintModel
		'''
		return self.compliant(crom) and croi.compliant(crom) and self.axiom13(crom,croi) and \
		self.axiom14(crom,croi) and self.axiom15(crom,croi) and self.axiom16(crom,croi)
		
	def axiom13(cm,crom,croi):
		'''
		\\forall ct \\in CT \\forall (i..j,a) \\in \\text{rolec}(ct) \\forall c \\in C_{ct} :
		i \\leq \\big(\\sum\\nolimits_{o \\in O^c}{a^{\\I^c_o}}\\big) \\leq j
		'''
		return all( \
		crd[0] <= sum( [evaluate(a,croi,o,c) for o in croi.o_c(c)] ) <= crd[1] \
		for ct in crom.ct if ct in cm.rolec	for crd,a in cm.rolec[ct] for c in croi.c if croi.type1[c]==ct )
		
	def axiom14(cm,crom,croi):
		'''
		\\forall (o,c,r) \\in \\text{plays} \\forall(crd,a) \\in \\text{rolec}(\\text{type}(c)) :
		\\text{type}(r) \\in \\text{atoms}(a) \\Rightarrow a^{\\I^c_o} = 1
		'''
		return all( evaluate(a,croi,o,c)==1 for o,c,r in croi.plays if croi.type1[c] in cm.rolec for crd,a in cm.rolec[croi.type1[c]] if croi.type1[r] in atoms(a) )
		
	def axiom15(cm,crom,croi):
		'''
		\\forall rst \\in RST \\forall c \\in C \\forall (r_1,r_2) \\in \\text{links}(rst,c) :
		\\text{card}(rst)=(i..j,k..l) \\wedge
		\\big( r_2 \\neq \\varepsilon \\Rightarrow i \\leq \\big| \\text{pred}(rst,c,r_2) \\big| \\leq j \\big) \\wedge
		\\big( r_1 \\neq \\varepsilon \\Rightarrow k \\leq \\big| \\text{succ}(rst,c,r_1) \\big| \\leq l \\big)		
		'''
		return all( \
		( cm.card[rst][0][0] <= len( croi.pred(rst,c,r_2) ) <= cm.card[rst][0][1] ) and \
		( cm.card[rst][1][0] <= len( croi.succ(rst,c,r_1) ) <= cm.card[rst][1][1] ) \
		for rst in crom.rst if rst in cm.card for c in croi.c if (rst,c) in croi.links for r_1,r_2 in croi.links[(rst,c)] )

	def axiom16(cm,crom,croi):
		'''
		\\forall c \\in C \\forall (rst,f) \\in intra:\\text{links}(rst,c) = \\emptyset\\ \\vee
		f(\\overline{\\text{links}(rst,c)})=1
		'''
		return all( f( croi.overline_links(rst,c) )==1 for c in croi.c for rst,f in cm.intra if (rst,c) in croi.links) 	
