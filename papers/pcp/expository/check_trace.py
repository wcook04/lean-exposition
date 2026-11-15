"""Finite honest-address illustration; no general soundness or Lean replay claim."""
import json

# F4 = F2[omega]/(omega^2+omega+1), bit 0 is the coefficient of 1.
def add(x, y): return x ^ y

def mul(x, y):
    a,b=x&1,(x>>1)&1
    c,d=y&1,(y>>1)&1
    return (a*c ^ b*d) | ((a*d ^ b*c ^ b*d) << 1)

def sq(x): return mul(x,x)
def cube(x): return mul(sq(x),x)
def chi(x): return add(1,mul(3,x))
def Z(x): return add(sq(x),x)
def M(x,u): return mul(u,add(x,3))
def l_first(x): return x&1
def l_second(x): return (x>>1)&1
def l_sum(x): return l_first(x)^l_second(x)
def phi(y): return (1,y,sq(y))
def inner_a(w): return w[2]^w[1]
def inner_b(w): return w[2]^w[0]
def label(coeffs,x):
    a,b=x&1,(x>>1)&1
    values=(1,a,b,a*b)
    return sum(((coeffs>>i)&1)*values[i] for i in range(4))%2

def pname(v):
    return ['0','1','omega','omega^2'][v]

for x in range(4):
    assert add(cube(chi(x)),1)==mul(Z(x),add(x,3))
    assert M(x,0)==0
    assert M(x,Z(x))==add(cube(chi(x)),1)
    assert l_sum(x)==l_first(mul(3,x))
    assert l_second(x)==l_first(mul(2,x))
    assert label(15,x)==l_first(add(cube(x),1))
for y in range(4):
    assert M(2^y,y)==sq(y)^y
    assert M(2^y,1^y)==sq(y)^1
    assert inner_a(phi(y))==sq(y)^y
    assert inner_b(phi(y))==sq(y)^1
# Check interpolation identity on every degree <=1 affine row in F4^3
for c0 in range(4):
 for c1 in range(4):
  for c2 in range(4):
   for c3 in range(4):
    def p(w): return c0^mul(c1,w[0])^mul(c2,w[1])^mul(c3,w[2])
    for w0 in range(4):
     for w1 in range(4):
      for w2 in range(4):
       w=(w0,w1,w2)
       plus1=(w0,w1^2,w2)
       plus2=(w0,w1^3,w2)
       assert p(w)==mul(3,p(plus1))^mul(2,p(plus2))
rows=[]
for name,target,fn in [('A',(2,0),inner_a),('B',(2,1),inner_b)]:
    for purpose,z in [('comparison',1),('return',0)]:
        w=phi(z)
        points=[(w[0],w[1]^2,w[2]),(w[0],w[1]^3,w[2])]
        vals=list(map(fn,points))
        bits=[l_sum(vals[0]),l_second(vals[1])]
        got=bits[0]^bits[1]
        wanted=l_first(M(target[0]^z,target[1]^z))
        assert got==wanted
        rows.append({'target':name,'target_point':list(map(pname,target)),
          'purpose':purpose,'z':z,'inner_target':list(map(pname,w)),
          'inner_points':[list(map(pname,p)) for p in points],
          'field_values':list(map(pname,vals)),
          'labels':['Z1+Z2','Z2'],'bits':bits,'xor':got,
          'expected_primary_bit':wanted})
for r in range(16):
    assert label(r,chi(2))^label(r^15,chi(2))==1
result={
 'scope':'Exact honest subroutine-address illustration over F4; not a production parameter instance, complete verifier, statistical soundness check, or Lean replay.',
 'colouring':[pname(chi(0)),pname(chi(1))],
 'ambient_point':'omega','chi_at_point':pname(chi(2)),
 'Z_at_point':pname(Z(2)),
 'Val_at_point':pname(add(cube(chi(2)),1)),
 'masked_derived_query':{'labels':['Z1','1+Z2+Z1*Z2'],'bits':[label(2,0),label(13,0)],'xor':1},
 'corrections':rows,
 'assertions':['all four field points satisfy the colouring-certificate identity',
   'all four line parameters satisfy both displayed restrictions and digit evaluations',
   'all 4^4 affine functions on F4^3 and all 4^3 targets satisfy the fixed-direction two-node interpolation identity',
   'all 16 masks return the honest derived bit',
   'all eight auxiliary read values, two primary comparison bits, and final ZERO equalities match'],
 'final_zero_equalities':{'b0':0,'bZ':1,'derived_p':1,'accepts':True}
}
print(json.dumps(result,indent=2))
