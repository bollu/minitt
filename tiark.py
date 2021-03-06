#!/usr/bin/env python3
# https://tiarkrompf.github.io/notes/?/dependent-types/aside4

import json

nVars = 0

# ===Untyped LC===

# new names
def fresh():
    global nVars
    out = f"x{nVars}"
    nVars += 1
    return out

# HOAS
def struct(e):
    if isinstance(e, list):
        return list(map(struct, e))
    if callable(e):
        x = fresh()
        return [x, struct(e(x))]
    return e

# printing
def stringify(e):
    global nVars
    save = int(nVars)
    return json.dumps(struct(e))
    nVars = save


test = ["fun", lambda x: ["app", ["fun", lambda y: y], x]]
# ["fun", ["x0", ["app", ["fun", ["x1", "x1"]], "x0"]]]
print(stringify(test))

# Exercise: implement hoas as inverse of struct. Hint: use substitution.
# need to deeply replace all occurences of symbol with x
def replace(old, new, e):
    if isinstance(e, list):
        return [replace(old, new, x) for x in e]
    if e == old:
        return new
    return old
def hoas(s):
    assert isinstance(s, list)
    if s[0] == "fun":
        varname = s[1][0]
        e = s[1][1]
        return lambda x: hoas(replace(varname, x, e))
    if s[0] == "app":
        return ["app", hoas(s[1])]
# -----
# tagless final

def tagless_fun(f): 
    return ["fun", f]

def tagless_app(f, a): 
    return ["app", f, a]

nVars = 0
test = tagless_fun(lambda x: tagless_app(tagless_fun(lambda y: y), x))
# ["fun",["x0",["app",["fun",["x1","x1"]],"x0"]]]
print(stringify(test))



# -----
# NBE

def nbe_fun(f): return ["fun", f]
def nbe_app(f , a):
    if  f[0] == "fun" : return f[1](a)
    return ["app", f, a]

nVars = 0
test = nbe_fun(lambda x: nbe_app(nbe_fun(lambda y: y), x))
print(stringify(test))

# ----
# NBE, take 2

def struct(e):
  if isinstance(e, list): 
      return list(map(struct, e))
  if callable(e):
      x = fresh()
      return ["=>", x, struct(e(x))]
  return e

def fun(f): return f

def app(f, a):
  if callable(f): return f(a)
  return [f, a]

test = fun(lambda x: app(x, lambda y: y))
print(stringify(test))

# ===STLC===
print("===STLC===")

def isfun0(f): return callable(f)
def fun0(f): assert(isfun0(f)); return f
def app0(f,a):
    if (isfun0(f)): return f(a)
    else: return [f, a]

def isbasetype(t): return isinstance(t, str)
def isfuntype(t): return isinstance(t, list) and t[0] == "->"
def istype(t): return isfuntype(t) or isbasetype(t)

def funtype(atp,rtp):
  assert istype(atp), f"illegal arg type: {atp}" 
  assert istype(rtp), f"illegal res type: {rtp}" 
  return ["->", atp, rtp]

def typed(e,t): return ["typed", e, t]
def istyped(f): return isinstance(f, list) and f[0] == "typed"
def untyped(e): assert istyped(e), f"no type: {e}"; return e[1:]

def printt(e):
  [tm, ty] = untyped(e)
  print(f"term: {stringify(tm)}")
  print(f"type: {stringify(ty)}")

def fun(atp, f):
  assert istype(atp), f"illegal arg type: {atp}"
  return typed(
          fun0(lambda x : untyped(f(typed(x,atp)))[0]),
          funtype(atp, untyped(f(typed("x?",atp)))[1]))


def app(f,a):
  [fv, ftp] = untyped(f)
  [av, atp] = untyped(a)
  assert isfuntype(ftp), f"not a function: {f}"

  # paramty, argty
  [_,ptp,rtp] = ftp
  assert stringify(atp) == stringify(ptp), f"type mismatch: {stringify(atp)} != {stringify(ptp)}"
  res = app0(fv, av)
  return typed(res, rtp)


def constant(tm,ty):
  assert(istype(ty), "illegal type: "+ty)
  return typed(tm, ty)


nVars = 0
intId = fun("Int", lambda x: x)
printt(intId)

nVars = 0
eta = fun(funtype("Int","Int"), lambda f: fun("Int", lambda x: app(f,x)))
printt(eta)
etaIntId = app(eta, fun("Int", lambda x: x))
printt(etaIntId)

# ===Dependent types (COC)===
print("===COC===")

def isfun0(f): return callable(f)
def fun0(f): assert(isfun0(f)); return f
def app0(f,a):
    if (isfun0(f)): return f(a)
    else: return [f, a]

def forall0(atp,f): return ["forall", atp, f] 
def isforall0(f): return isinstance(f, list) and f[0] == "forall"

def typed(e,t):
    # create a real function.
    o = lambda a: app(o,a)
    o.untyped = e; o.type = t
    return o

def istyped(e): return hasattr(e, "untyped") and hasattr(e, "type")
def untyped(e): assert istyped(e), f"no type: {e}"; return [e.untyped, e.type]

def forall(atp,f):
    [atpt, atpk] = untyped(atp)
    assert atpk == "Type" or atpk == "Kind", f"illegal arg type/kind: {atpk}"
    [res, tpe] = untyped(f(typed("x?",atpt)))
    return typed(forall0(atpt, lambda x: untyped(f(typed(x,atpt)))[0]), tpe)

def fun(atp,f):
    [atpt,atpk] = untyped(atp)
    assert atpk == "Type" or atpk == "Kind", f"illegal arg type/kind: {atpk}"
    return typed(
          fun0(lambda x: untyped(f(typed(x,atpt)))[0]),
          forall0(atpt, lambda x: untyped(f(typed(x,atpt)))[1]))

def app(f,a):
    [f1,ftp] = untyped(f)
    [a1,atp] = untyped(a)
    assert(isforall0(ftp), f"not a function: {f}")
    [key,ptp,frtp] = ftp

    # TODO: why do I need this hack..?
    global nVars
    nVars = 0; str_atp = stringify(atp)
    nVars = 0; str_ptp = stringify(ptp)
    assert  str_atp == str_ptp, f"type mismatch: {str_atp} != {str_ptp}"
    res = app0(f1, a1)
    rtp = frtp(a1)
    return typed(res,rtp)

def constant(tm,ty):
    [tyt,tyk] = untyped(ty)
    assert tyk == "Type" or tyk == "Kind", f"illegal arg type/kind: {tyk}"
    return typed(tm,tyt)
Type = typed("Type","Kind")

print("typeId:")
nVars = 0
typeId = fun(Type, lambda t: t)
printt(typeId)

print("polyId:")
nVars = 0
polyId = fun(Type, lambda t: fun(t, lambda x: x))
printt(polyId)

N = constant("N",Type)
z = constant("z",N)
s = constant("s",forall(N, lambda x: N))

three = s(s(s(z)))
print("three:")
printt(three)

ff = lambda T: forall(T, lambda x: T) # fun type T->T
ChurchT = forall(Type, lambda N: forall(N, lambda z: forall(ff(N), lambda s: N)))
ChurchN = lambda f: fun(Type, lambda N: fun(N, lambda z: fun(ff(N), lambda s: f(N)(z)(s))))
peano = fun(ChurchT, lambda n: n(N)(z)(s))

print("church three:")
nVars = 0
threeChurch = ChurchN(lambda N:  lambda z: lambda s: s(s(s(z))))
printt(threeChurch)

print("peano three:")
printt(peano(threeChurch))

# this chokes
plus = fun(ChurchT, lambda a: fun(ChurchT, lambda b: ChurchN(lambda N: lambda z: lambda s: a(N)(b(N)(z)(s))(s))))
sixChurch = plus(threeChurch)(threeChurch)

print("peano plus(three, three):")
printt(peano(sixChurch))
