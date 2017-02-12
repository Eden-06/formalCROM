#!/usr/bin/env python
# -*- coding: UTF-8 -*-

"""cromtest.py: Encompasses test cases for the various defintions."""

__author__ = "Thomas Kühn"
__copyright__ = "Copyright 2014"
__license__ = "MIT"
__version__ = "1.0.0"

from crom import *

print "Testing... Basic Defintions"
# Test Basic Defintions

totaltests=[ ([],{1:1},True), ([1,2],{1:1,2:2},True), ([1,2],{1:1},False), ([1],{},False) ]
for d,f,e in totaltests:
	assert total_function(d,f)==e, "Case total_function({0},{1})!={2}".format(d,f,e)
	
disjointtests=[([set(),set()],True), 
               ([set([1,2]),set([3,4])],True),
               ([set(),set([1]),set([1])],False),
               ([set([1,2,3]),set([3,4,5])],False)]
for s,e in disjointtests:
	assert mutual_disjoint(s)==e, "Case mutual_disjoint({0})!={1}".format(s,e)

# Test Cases for CROM

print "Testing... CROM"

test0=CROM([],[],[],[],[],{},{})
test1=CROM([1],[2,3],[4],['a'],[(1,2),(1,3)],{4:[2,3]},{'a':(2,3)})
test2=CROM([1],[2,3],[4],['a'],[(1,2)],{4:[2,3]},{'a':(2,3)})
test3=CROM([1],[2,3],[4,5],['a'],[(1,2),(1,3)],{4:[2,3],5:[]},{'a':(2,3)})
test4=CROM([1],[2,3],[4,5],['a'],[(1,2),(1,3)],{4:[2,3],5:[2]},{'a':(2,3)})
test5=CROM([1],[2,3],[4],['a'],[(1,2),(1,3)],{4:[2,3]},{'a':(2,2)})
test6=CROM([1],[2,3],[4,5],['a'],[(1,2),(1,3)],{4:[2],5:[3]},{'a':(2,3)})
test7=CROM([1],[2,3,4],[5,6],['a'],[(1,2),(1,3)],{5:[3],6:[]},{'a':(2,2)})


cromtests=[(test0,True,True,True,True,True),
           (test1,True,True,True,True,True),  (test2,False,True,True,True,True),
           (test3,True,False,True,True,True), (test4,True,True,False,True,True),
           (test5,True,True,True,False,True), (test6,True,True,True,True,False),
           (test7,False,False,False,False,False)]

for t,a1,a2,a3,a4,a5 in cromtests:
	assert(t.axiom1()==a1)
	assert(t.axiom2()==a2)
	assert(t.axiom3()==a3)
	assert(t.axiom4()==a4)
	assert(t.axiom5()==a5)
	assert(t.wellformed()==(a1 and a2 and a3 and a4 and a5))
	
# Test Cases for CROI

print "Testing... CROI"

test8=CROI([1],[2,3],[4],{1:1,2:2,3:3,4:4},[(1,4,2),(1,4,3)],{('a',4):[(2,3)]} )
test8b=CROI([],[],[],{},[],{} )
test9=CROI([1],[2,3],[4],{1:1,2:5,3:3,4:4},[(1,4,2),(1,4,3)],{('a',4):[(2,3)]} )
test10=CROI([1],[2,3],[4],{1:1,2:2,3:2,4:4},[(1,4,2),(1,4,3)],{('a',4):[(2,None),(3,None)]} )
test11=CROI([1],[2,3],[4,5],{1:1,2:2,3:3,4:4,5:4},[(1,4,2),(1,5,2),(1,4,3)],{('a',4):[(2,3)]} )
test11b=CROI([1,5],[2,3],[4],{1:1,2:2,3:3,4:4,5:1},[(1,4,2),(5,4,2),(1,4,3)],{('a',4):[(2,3)]} )
test12=CROI([1],[2,3],[4],{1:1,2:2,3:3,4:4},[(1,4,2),(1,4,3)],{('a',4):[(2,3), (None,None)]} )
test13=CROI([1,6],[2,3,5],[4],{1:1,2:2,3:3,4:4,5:3,6:1},[(1,4,2),(1,4,3),(6,4,5)],{('a',4):[(2,3)]} )
test13b=CROI([1,6],[2,3,5],[4],{1:1,2:2,3:3,5:2,6:1,4:4},[(1,4,2),(1,4,3),(6,4,5)],{('a',4):[(2,3)]} )
test14=CROI([1],[2,3],[4],{1:1,2:2,3:3,4:4},[(1,4,2),(1,4,3)],{('a',4):[(2,3),(2,None)]} )
test14b=CROI([1],[2,3],[4],{1:1,2:2,3:3,4:4},[(1,4,2),(1,4,3)],{('a',4):[(2,3),(None,3)]} )
test15=CROI([1],[2,3,5,6],[4],{1:1,2:5,3:3,4:4,5:3,6:2},[(1,4,2),(1,4,5),(1,4,3)],{('a',4):[(2,3),(None,None),(2,None)]} )

croitests=[ (test8, True,True,True,True,True,True),
            (test8b, True,True,True,True,True,True),
            (test9, False,True,True,True,True,True),
            (test10,True,False,True,True,True,True),
            (test11,True,True,False,True,True,True),
            (test11b,True,True,False,True,True,True),
            (test12,True,True,True,False,True,True),
            (test13,True,True,True,True,False,True),
            (test13b,True,True,True,True,False,True),
            (test14,True,True,True,True,True,False),
            (test14b,True,True,True,True,True,False),
            (test15,False,False,False,False,False,False)]

for t,a6,a7,a8,a9,a10,a11 in croitests:
	assert(t.axiom6(test1)==a6)
	assert(t.axiom7(test1)==a7)
	assert(t.axiom8(test1)==a8)
	assert(t.axiom9(test1)==a9)
	assert(t.axiom10(test1)==a10)
	assert(t.axiom11(test1)==a11)
	assert(t.compliant(test1)==(a6 and a7 and a8 and a9 and a10 and a11))

# Test Cases for Role Groups

print "Testing... RoleGroups"
testrg1=2
testrg2=RoleGroup([2,3],2,2)
testrg3=RoleGroup([RoleGroup([2,RoleGroup([3],1,2)],0,1),2],1,1)
testrg4=RoleGroup([],0,0)
testrg5=RoleGroup([],1,1)
testrg6=RoleGroup([2],0,0)
testrg7=RoleGroup([5],0,0)
rgtests=[ (testrg1,set([2]),1),   (testrg2,set([2,3]),1),
          (testrg3,set([2,3]),1), (testrg4,set(),1),
          (testrg5,set(),0),     (testrg6,set([2]),0),
          (testrg7,set([5]),1) ]  

for t,s,e in rgtests:
	assert( atoms(t) == s )
	assert( evaluate(t,test8,1,4) == e)

# Testing Constraint Models

print "Testing... ConstraintModel"

#test1=CROM([1],[2,3],[4],['a'],[(1,2),(1,3)],{4:[2,3]},{'a':(2,3)})

order=lambda r: all( x<=y for x,y in r)
rgxor=RoleGroup([2,3],1,1)

testcm0=ConstraintModel({},{},[])
testcm1=ConstraintModel({4: [((1,3),rgxor)] },{ 'a':((1,1),(1,1)) },[('a',order)])
testcm2=ConstraintModel({4: [((1,1),2)] },{ 'a':((1,1),(1,1)) },[])
testcm3=ConstraintModel({4: [((1,1),2)] },{},[])
testcm4=ConstraintModel({4: [((1,1),5)] },{},[])
testcm5=ConstraintModel({5: [((1,1),2)] },{},[])

cmtests=[ (testcm0, True), (testcm1, True), (testcm2, True),
          (testcm3, True), (testcm4, False), (testcm5, True)]

for t,a12 in cmtests:
	assert( t.axiom12(test1)==a12 )
	assert( t.compliant(test1)==a12 )
	
assert(testcm0.compliant(test0))

# Testing Validity

print "Testing... Validity"

test16=CROI([1,5],[2,3],[4],{1:1,2:2,3:3,4:4,5:1},[(1,4,2),(5,4,3)],{('a',4):[(2,3)]} )
test17=CROI([1,0],[2,3],[4],{1:1,2:2,3:3,4:4,0:1},[(1,4,2),(0,4,3)],{('a',4):[(2,3)]} )
test18=CROI([1,5,6],[2,3,7],[4],{1:1,6:1,2:2,3:3,7:3,4:4,5:1},[(1,4,2),(5,4,3),(6,4,7)],{('a',4):[(2,3),(2,7)]} )
test18b=CROI([1,5,0],[2,3,7],[4],{1:1,0:1,2:2,3:3,7:2,4:4,5:1},[(1,4,2),(5,4,3),(0,4,7)],{('a',4):[(2,3),(7,3)]} )
test19=CROI([1,5,6],[2,3,7,8],[4],{1:1,5:1,6:1,2:2,3:3,7:2,8:3,4:4},[(1,4,2),(5,4,3),(5,4,7),(6,4,8)],{('a',4):[(2,3),(7,8)]} )
test20=CROI([1,5,6,9],[2,3,7,8],[4],{1:1,5:1,6:1,9:1,2:2,3:3,7:2,8:3,4:4},[(1,4,2),(5,4,3),(6,4,7),(9,4,8)],{('a',4):[(2,3),(7,8)]} )

# TODO: Test for inter-relationship constraint issue with links(rst1,c)={(n1,n2)} and links(rst2,c)={(n1,None),(None,n2)} with constrain rst1 

valtests=[ (test0,testcm0,test8,False, True, True, True, True),
           (test0,testcm0,test8b,True, True, True, True, True),
           (test1,testcm0,test8,True, True, True, True, True), 
           (test1,testcm0,test8b,True, True, True, True, True),
           (test0,testcm1,test8,False, True, False, True, True), 
           (test0,testcm1,test8b,True, True, True, True, True),
           (test1,testcm1,test8,True, False, False, True, True), 
           (test1,testcm1,test8b,True, True, True, True, True),
           (test1,testcm1,test16,True, True, True, True, True), 
           (test1,testcm1,test17,True, True, True, True, False), 
           (test1,testcm1,test18,True, True, True, False,True),
           (test1,testcm1,test18b,True, True, True, False,True),
           (test1,testcm1,test19,True, True, False, True, True),
           (test1,testcm1,test20,True, False, True, True, True)]

for m,c,i,co,a13,a14,a15,a16 in valtests: 
	assert( i.compliant(m) == co)
	assert( c.axiom13(m,i) == a13)
	assert( c.axiom14(m,i) == a14)
	assert( c.axiom15(m,i) == a15)
	assert( c.axiom16(m,i) == a16)
	assert( c.validity(m,i) == (co and a13 and a14 and a15 and a16))

print "Test completed successfully"
