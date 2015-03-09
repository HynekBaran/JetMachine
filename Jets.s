print(`JETS 5.0`);

# Jets -- Differential calculus on jet spaces and diffieties
#
# (c) 1999-2004 by Michal Marvan
#
# Instructions: (1) Read this file into a fresh Maple session.
# (2) Check the installation by reading in the file Jet.t (if any)

print(`Differential calculus on jet spaces and diffieties`);
print(`for Maple 6, 7, 8, 9`);
print(`as of 12 July 2004`);

#
#  L i c e n s e
#

# JETS is a free software distributed under the terms of the GNU General 
# Public License <http://www.gnu.org/copyleft/gpl.html> as published by 
# the Free Software Foundation.
#
# In particular, JETS comes with ABSOLUTELY NO WARRANTY.

#
#  C h a n g e s   i n   M a p l e   s y n t a x
#

Existing := proc(c,a) assigned(c||a) end:
Call := proc(c,a) c||a end:
# || replaces . since 6.0

#
#  D e c l a r a t i o n s
#

# A procedure whose purpose is to change settings of global variables 
# is called a declaration.
# If named in plural, it resets the previous declaration.
# If named in singular, it has a cummulative effect.

#
#  A u x i l i a r y   p r o c e d u r e s
#
    
size := proc(a)
  evalf(nops(Vars(a)) + length(a)/1000000000)
end:

# sorting by size

sizesort := proc(ql,pr)  # ql = list of expressions, pr = sizeing proc
  local qls;
  qls := map(proc(q,pr) [q,pr(q)] end, ql, pr);
  qls := sort(qls, proc(a,b) evalb(op(2,a) < op(2,b)) end);
  map (proc(a) op(1,a) end, qls)
end:

# reducing products

reduceprod :=  proc(a)   
  if type (a,`^`) then
    if type (op(2,a), posint) then procname(op(1,a))
    elif type (op(2,a), negint) then 1
    else a
    fi
  elif type (a,`*`) then convert(map(procname,[op(a)]),`*`)
  else a
  fi
end:

#
#  V a r i a b l e s 
#

# Declaration of coordinates (only plural form):

coordinates := proc (blist,flist)
  global `b/var/list`,`b/var/s`,`b/dim`,`b/<</list`,
    `f/var/list`,`f/var/s`,`f/dim`,`f/<</list`;
  if nargs = 0 then
    ERROR(`arguments should be:\n
[list of base variables], [list of fibre variables], optional maxorder`) 
  fi;
  if not type([op(blist)], list(name)) then
    ERROR(`base coordinates must be unassigned names`)
  fi;
  if not type([op(flist)], list(name)) then
    ERROR(`fibre coordinates must be unassigned names`)
  fi;
  if nops([op(blist),op(flist)]) <> nops({op(blist),op(flist)}) then
    ERROR(`coordinates must be mutually different`)
  fi;
  `b/var/list` := blist;
  `b/var/s` := {op(blist)};
  `b/dim` := nops(`b/var/s`);
  `b/<</list` := `b/var/list`:
  `f/var/list` := flist;
  `f/var/s` := {op(flist)};
  `f/dim` := nops(`f/var/s`);
  `f/<</list` := `f/var/list`;
  noderives():
  refresh ();
# Result:
  if nargs > 2 then `jet/aliases`(`f/var/list`,args[3])
  else `b/var/list`, `f/var/list`
  fi
end:

`b/var/list` := []: `b/var/s` := {}: `b/dim` := 0:
`f/var/list` := []: `f/var/s` := {}: `f/dim` := 0:

# Type checking procedures:

`type/b/var` := proc (x) member (x, `b/var/s`) end:
`type/f/var` := proc (f) member (f, `f/var/s`) end:

# Jet variables are unassigned calls to 'jet'.

`type/j/var` := specfunc(anything,jet):

# Variables are of type 'var'.

`type/var` := proc(x)
  if type (x,'name') then type (x,{`b/var`, `f/var`})
  else type (x,specfunc(anything,jet))
  fi
end:

#
#  C o u n t s 
#

# A count is a product of nonnegative integer powers, but 1 is not a count.

`type/count` := proc (x) 
  local x1;  
  if type (x,`^`) then type (op(2,x), posint) 
  elif type (x,`*`) then
    for x1 in x do if not type (x1,'count') then RETURN(false) fi od;
    true
  elif x = 1 then false
  else true
  fi
end:

# A count is proper when it is a product or a power

`type/count/proper` := {`*`,`^`}:

# A count is of first order when it is neither a product nor a power

`type/count/1order` := proc(x) not type(x,`count/proper`) end:

# A b/count is a product of nonnegative integer powers of base variables,
# but 1 is not a b/count.

`type/b/count` := proc (x) 
  local x1;  
  if type (x,`^`) then type (op(1,x),`b/var`) and type (op(2,x), posint) 
  elif type (x,`*`) then
    for x1 in x do if not type (x1,`b/count`) then RETURN(false) fi od;
    true
  else type (x,`b/var`)
  fi
end:

# Dealing with counts: 
# `count/f`(x) := the first ``factor'' of the count x;
# `count/r`(x) := x/`count/f`(x);
# `count/length`(x) := the sum of the powers in x;
# `count/sgn`(x) := the parity of `count/length`x;
# `transform/count`(x) :=  the product of non-negative powers in x
# (transforms x into 1 or count).

`count/f` := proc (x)
  if type (x,`^`) then op(1,x)
  elif type (x,`*`) then `count/f`(op(1,x))
  else x
  fi
end:

`count/r` := proc (x)
  if type (x,`^`) then x/op(1,x)
  elif type (x,`*`) then x/`count/f`(op(1,x))
  else NULL
  fi
end:

`count/length` := proc (x)
  if x = 1 then 0 
  elif type (x,`^`) then op(2,x)
  elif type (x,`*`) then convert (map (`count/length`, [op(x)]), `+`)
  else 1
  fi
end:

`count/sgn` := proc (x) 1 - 2*(`count/length`(x) mod 2) end:

`transform/count` := proc(x)
  local aux;
  if type (x,`^`) then if op(2,x) < 0 then 1 else x fi
  elif type (x,`*`) then aux := map(`transform/count`, x);
  else x
  fi
end:

# Jet order of a variable q

varorder := proc(q)
  if type(q,'name') then 0
  else `count/length`(op(2,q))
  fi
end:

jetorder := proc(f)
  local js;
  js := sort([op(map(varorder,vars(f)))]);
  op(nops(js),js)
end:

# Creating aliases for jet variables. Arguments are:
# f1,...,fn,r, where r = jet order and 
# f's are fibre variables (optional)

`jet/aliases` := proc ()
  global `b/var/list`;
  local aux,flist,r;
  r := args[nargs];
  if nargs = 1 then flist := `f/var/list` 
  else flist := args[1..nargs-1] 
  fi;
  if not type (`b/var/list`,'list'(symbol)) then
    ERROR (`base variables must be symbols`) 
  fi;
  aux := expand((1 + convert(`b/var/s`,`+`))^r - 1);
  aux := map(proc(a) a/coeffs(a) end, [op(sort(aux, `b/var/list`))]);
  alias(op(map(proc(u,aux) if type(u,symbol) then
        op(map(proc(x,u) cat(u,'_',`bcount//str`(x)) = 'jet'(u,x) end,
          aux, u))
      else
        op(map(proc(x,u)
            cat(op(0,u),'_',`bcount//str`(x))[op(u)] = 'jet'(u,x)
          end, aux, u))
      fi
    end, flist, aux)));
end:

`bcount//str` := proc (x)
  if type (x,'name') then x
  elif type (x,`^`) then 
    if op(2,x) > 3 then cat(op(2,x),op(1,x)) else op(1,x) $ op(2,x) fi
  elif type (x,`*`) then `bcount//str/_`(op(map(`bcount//str`, [op(x)])))
  else ERROR (`not a count`, x)
  fi 
end:

`bcount//str/_` := proc ()
  local i,a,b,ans;
  ans := args[1];
  for i from 2 to nargs do
    a := args[i-1]; b := args[i];
    if length(a) + length(b) > 2 then ans := ans,`_`,b else ans := ans,b fi
  od 
end:

`count//seq` := proc (x)
  if type (x,`^`) then `count//seq`(op(1,x)) $ op(2,x)
  elif type (x,`*`) then op(map(`count//seq`,[op(x)]))
#  elif type (x,symbol) then x
#  else cat(op(1,x),'_',`bcount//str`(op(2,x))) 
  else x
  fi
end:

#
#  N a m e s
#

`name/tab` := table([]):

# Unassigned names may acquire a meaning through a declaration.
# Such names are said to be registered.
# For example, variables are registered names since they are declared
# through the coordinates command.

# Meanings other than 'variable' are stored in `name/tab`.
# registered() prints meanings of all names;
# registered(a) prints all names of meaning a;

# WARNING: After  a s s u m e,  names lose their registration and must be
# registered again.

registered := proc() 
  local a;
  if nargs = 0 then
    op(select(proc(e) op(1,e) = eval(op(1,e)) end, op(2,op(`name/tab`))))
  else a := args[1];
    op(map(proc(e,a) op(1,e) end, select(
      proc(e,a)
        op(1,e) = eval(op(1,e)) and type(op(1,e),a) 
      end, op(2,op(`name/tab`)), a), a))
  fi
end:

# To clear a declaration from all names:

clear := proc()
  local a,aux,ans;
  aux := select(type,{args},'name');
  if aux <> {args} then
    ERROR(`not a name`, op({args} minus aux)) 
  fi;
  aux := select(proc(a) Existing(`clear/`,a) end, aux);
  if aux <> {args} then
    ERROR(`invalid argument`, op({args} minus aux)) 
  fi;
  ans := NULL;
  for a in aux do ans := ans, Call(`clear/`,a)() od;
end:

#
#   P a r a m e t e r s
#

parameter := proc()
  global `name/tab`;
  local a,aux;
  aux := select (type,{args},name);
  if aux <> {args} then ERROR(`not a name`, op({args} minus aux)) fi;
  aux := select(
    proc(a)
      type (a,'dep')
      or type (a,{`b/var`,`f/var`,'constant'})
      or (type (`name/tab`[a],'set')
        and `name/tab`[a] minus {'parameter','nonlocal'} <> {})
    end, {args});
  if aux <> {} then ERROR (`name(s) already used`, op(aux)) fi;
  for a in [args] do 
    if type (`name/tab`[a],'set') then
      `name/tab`[a] := `name/tab`[a] union {'parameter'}
    else `name/tab`[a] := {'parameter'}
    fi
  od;
  registered('parameter')
end:

`clear/parameter` := proc()
  local a,aux;
  global `name/tab`;
  aux := {registered('parameter')};
  for a in aux do
    `name/tab`[a] := `name/tab`[a] minus {'parameter'} 
  od;
  op(aux)
end:

parameters := proc()
  `clear/parameter`();
  parameter(args)
end:

# Parameters are of type 'parameter':

`type/parameter` := proc (x)
  if type (`name/tab`[x],'set') then
    member ('parameter',`name/tab`[x])
  else false
  fi
end: 

# Type 'ar' is either 'parameter' or 'var':

`type/ar` := {'var','parameter'}:

`type/ar/count` := proc (x) 
  local x1;  
  if x = 1 then false 
  elif type (x,`^`) then type (op(1,x),'ar') and type (op(2,x), posint) 
  elif type (x,`*`) then
    for x1 in x do if not type (x1,`ar/count`) then RETURN(false) fi od;
    true
  else type (x,'ar')
  fi
end:

#
#   D e p e n d e n c e
#

# Names may depend on variables:

dependence := proc ()
  local f,fs,es,e; 
  global `dep/tab`;
  fs := select(type, {args}, function);
  es := select(type, {args}, `=`);
  if fs union es <> {args} then
    ERROR (`wrong arguments`, op({args} minus fs minus es)) 
  fi; 
  es := es union map(proc(f) op(0,f) = {op(f)} end, fs);
  fs := select(
    proc(e)
      type (op(1,e),{`b/var`,`f/var`,'constant','parameter'})
    end, es);
  if fs <> {} then
    ERROR (`name(s) already used`, op(fs))
  fi; 
  for e in es do 
    if type (op(2,e), set('ar')) then `dep/tab`[op(1,e)] := op(2,e)
    else ERROR (`forbidden type of dependence`)
    fi
  od;
  refresh(); 
  es := {op(op(2,op(`dep/tab`)))};
  es := select(proc(e) evalb(op(1,e) = eval(op(1,e))) end, es);
  seq(op(1,e) = op(2,e), e = es)
end:

`dep/tab` := table ():

`type/dep` := proc(a) type(`dep/tab`[a],'set') end:

`clear/dependence` := proc()
  local e,el,ans;
  global `dep/tab`;
  el := op(2,op(`dep/tab`));
  ans := {seq((op(1,e))(op(op(2,e))), e = el)};
  `dep/tab` := table([]);
  ans 
end:

dependences := proc()
  `clear/dependence`();
  dependence(args)
end:

#
#   T o t a l   d e r i v a t i v e
#

TD := proc (f, x::`b/count`)
  global `EVALTD/s`,`EVALTD/b`,`EVALTD/n`;
  if nargs = 1 then RETURN (`TD~`(procname,f)) fi;
  if nargs > 2 then RETURN (TD(TD(f, args[2..nargs-1]), args[nargs])) fi;
  if type (f,'numeric') then 0
  elif type (f,'name') then
    if member (f,[constants]) then 0
    elif type (f,`b/var`) then if f = x then 1 else 0 fi
    elif type (f,`f/var`) then jet(f,x)
    elif type (f,'parameter') then 0
    elif type (f,'dep') then
      if vars(f) minus `b/var/s` = {} then pd(f,x)
      elif not `EVALTD/b` and not member(f,`EVALTD/s`)
        and `count/length`(x) > `EVALTD/n` then 'TD'(f,x) 
      elif type (x,'name') then 
        if type (f,'dep') then `TD/dep/s`(f,x,`dep/tab`[f]) fi
      else TD (TD(f,`count/f`(x)), `count/r`(x)) 
      fi
    elif Existing(`TD/indexed/`,op(0,f)) then
      Call(`TD/indexed/`,op(0,f))(op(f),x)
    else 'TD'(f,x)
    fi
  elif type (f,`+`) then map (procname, f, x)  
  elif type (f,'function') then 
    if type (f, `j/var`) then jet(op(1,f),x*op(2,f)) 
    elif type (f, specfunc(anything,pd)) then
      if type (op(1,f),'dep') then 
        if vars(op(1,f)) minus `b/var/s` = {} then pd(op(1,f), x*op(2,f))
        elif not `EVALTD/b` and not member (op(1,f),`EVALTD/s`)
          and `count/length`(x) > `EVALTD/n` then 'TD'(f,x)
        elif type (x,'name') then `TD/dep/s`(f,x,`dep/tab`[op(1,f)]) 
        else TD (TD(f,`count/f`(x)), `count/r`(x)) 
        fi
      else 'TD'(f,x)
      fi
    elif type (f, specfunc(anything,TD)) then 'TD'(op(1,f), x*op(2,f))
    elif type (x,'name') then
      if Existing(`der/`,op(0,f)) then
        Call(`der/`,op(0,f))(procname,op(f),x)
      else ERROR (`unexpected function`, f) 
      fi
    else TD (TD(f,`count/f`(x)), `count/r`(x))
    fi
  elif type (x,'name') then
    if type (f,`*`) then `der/*` (procname, f, x)
    elif type (f,`^`) then `der/^` (procname, op(1,f), op(2,f), x)
    else ERROR (`unexpected object`, f) 
    fi
  else TD (TD(f,`count/f`(x)), `count/r`(x))
  fi
end:

`TD~` := proc (pn,f)
  if type (pn,'indexed') then 
    if nops(pn) <> 1 then ERROR (`too many indices`, op(pn)) 
    else RETURN (TD(f,op(1,pn)))
    fi
  else eval(f)
  fi
end:

`TD/dep/s` := proc (f,x,s)
  convert(map(proc(p,f,x) pd(f,p)*TD(p,x) end, [op(s)], f,x), `+`)
end:

# Evaluating total derivatives

evalTD := proc (f) 
  local a,b,`EVALTD/b/old`,`EVALTD/s/old`;
  global `EVALTD/b`, `EVALTD/s`;
  `EVALTD/b/old` := `EVALTD/b`; `EVALTD/s/old` := `EVALTD/s`;
  if nargs = 1 then `EVALTD/b` := true
  elif type (args[2], set(name)) then `EVALTD/b` := false;
   `EVALTD/s` := args[2]
  else ERROR (`second argument must be a set of names`)
  fi; 
  b := eval(f); 
  a := {}; # a either different from a or evalTD(a) = a
  while hasfun(b,TD) and b <> a do
    a := b;
    b := traperror(eval(a))
  od;
  `EVALTD/b` := `EVALTD/b/old`; `EVALTD/s` := `EVALTD/s/old`;
  if b = lasterror then ERROR (lasterror) fi;
  b
end: 

`EVALTD/s` := {}:
`EVALTD/b` := false:
`EVALTD/n` := 0:

#
#   P a r t i a l   d e r i v a t i v e s
#

pd := proc (f, p::`ar/count`)
  if nargs = 1 then RETURN (`pd~`(procname,f)) fi;
  if nargs > 2 then RETURN(pd(pd(f, args[2..nargs-1]), args[nargs])) fi;
  if type (f,'numeric') then 0
  elif type (f,'name') then
    if member (f,[constants]) then 0
    elif type (f,'ar') then if f = p then 1 else 0 fi
    elif Existing (`pd/indexed/`,op(0,f)) then
      Call(`pd/indexed/`,op(0,f))(op(f),p)
    else `pd//tab`(f,p)
    fi
  elif type (f,`+`) then map (procname, f, p)  
  elif type (f,'function') then 
    if type (f, `j/var`) then if f = p then 1 else 0 fi
    elif type (f, specfunc(anything,pd)) then `pd//tab`(op(1,f), op(2,f)*p) 
    elif type (p,'ar') then
      if type (f, specfunc(anything,TD)) then `pd/TD`(op(f), p)     
      elif Existing(`der/`,op(0,f)) then
        Call(`der/`,op(0,f)) (procname,op(f),p)
      else `der//unknown`(procname,op(0,f),op(f),p)  # M.M. 26.11.2004
      fi
    else pd (pd(f,`count/f`(p)), `count/r`(p))
    fi
  elif type (p,'ar') then
    if type (f,`*`) then `der/*` (procname, f, p)
    elif type (f,`^`) then `der/^` (procname, op(1,f), op(2,f), p)
    else ERROR (`unexpected object`, f) 
    fi
  else pd (pd(f,`count/f`(p)), `count/r`(p))
  fi
end:

`pd~` := proc (pn,f)
  if type (pn,'indexed') then 
    if nops(pn) <> 1 then ERROR (`too many indices`, op(pn)) 
    else RETURN (pd(f,op(1,pn)))
    fi
  else eval(f)
  fi
end:

`pd/TD` := proc (f,x,p)
  option remember; 
  if type(x, 'name') then `pd/TD/1`(f,x,p)
  else `pd/TD/1`(evaln(TD(f,`count/r`(x))), `count/f`(x), p)
  fi
end:

`pd/TD/1` := proc (f,x,p)
  option remember; 
  local qs;
  qs := [op(vars(f))];
  TD(pd(f,p),x) + convert(map(
    proc(q,f,x,p)
      local qp; qp := pd(TD(q,x),p); 
      if qp <> 0 then pd(f,q)*qp else NULL fi end,
    qs, f, x, p), `+`)
end:

#
#   D e r i v a t i v e s   o f   f u n c t i o n s 
#

# For every concrete nary function  a  there should exist a function
# `der/f` of arguments  der,f1,...,fn,x  which returns the derivative
# der of a(f1,...,fn) with respect to x. The actual parameter der will
# eventually be one of pd, TD.

`der/` := proc (der,f,x) der(f,x) end:

`der/Diff` := proc (der,f,x) der(f,x) end:

`der/*` := proc (der,f,x) local i,s,di;
  s := 0;
  for i to nops(f) do di := der(op(i,f),x);
    if di <> 0 then s := s + subsop (i=di, f) fi
  od; s
end:

`der/&*` := proc ()
  local d,f,x,i,s,di;
  d := args[1];
  f := &*(args[2..nargs-1]); x := args[nargs];
  s := 0;
  for i to nops(f) do di := d(op(i,f),x);
    if di <> 0 then s := s + subsop (i=di, f) fi
  od; s
end:

`der/^` := proc (der,f,g,x)
  if type (g,'integer') then g*f^(g-1)*der(f,x)
  else g*f^(g-1)*der(f,x) + ln(f)*f^g*der(g,x)
  fi
end:

`der//unknown` := proc (der,f)  # M.M. 26.11.2004
  local as,x,i,ind;
  global DER;
  if type(f,'indexed') and op(0,f) = DER then 
    ind := op(f);
    if nargs = 4 then
      as := args[3]
    else ERROR(`wrong number of arguments`)
    fi;
    x := args[nargs];
    add(DER[op(sort([i,ind]))](as)*der(op(i,as), x), i = 1..(nargs - 3))
  else
    as := [args[3..(nargs - 1)]];
    x := args[nargs];
    add(DER[i](f(op(as)))*der(as[i], x), i = 1..(nargs - 3))
    fi
end:

`der/exp` := proc (der,f,x) exp(f)*der(f,x) end:
`der/ln`  := proc (der,f,x) der(f,x)/f end:

`der/sin` := proc (der,f,x) cos(f)*der(f,x) end:
`der/cos` := proc (der,f,x) -sin(f)*der(f,x) end:
`der/tan` := proc (der,f,x) der(f,x)/cos(f)^2 end:
`der/cot` := proc (der,f,x) -der(f,x)/sin(f)^2 end:
`der/csc` := proc (der,f,x) -cos(f)*der(f,x)/sin(f)^2 end:
`der/sec` := proc (der,f,x) sin(f)*der(f,x)/cos(f)^2 end:

`der/arcsin` := proc (der,f,x) der(f,x)/sqrt(1-f^2) end:
`der/arccos` := proc (der,f,x) -der(f,x)/sqrt(1-f^2) end:
`der/arccot` := proc (der,f,x) -der(f,x)/(1+f^2) end:
`der/arctan` := proc (der,f,x) der(f,x)/(1+f^2) end:

`der/sinh` := proc (der,f,x) cosh(f)*der(f,x) end:
`der/cosh` := proc (der,f,x) sinh(f)*der(f,x) end:
`der/tanh` := proc (der,f,x) der(f,x)/cosh(f)^2 end:
`der/coth` := proc (der,f,x) -der(f,x)/sinh(f)^2 end:
`der/csch` := proc (der,f,x) -cosh(f)*der(f,x)/sinh(f)^2 end:
`der/sech` := proc (der,f,x) -sinh(f)*der(f,x)/cosh(f)^2 end:

`der/arcsinh` := proc (der,f,x) der(f,x)/sqrt(1+f^2) end:
`der/arccosh` := proc (der,f,x) der(f,x)/sqrt(f^2-1) end:
`der/arccoth` := proc (der,f,x) der(f,x)/(f^2-1) end:
`der/arctanh` := proc (der,f,x) der(f,x)/(1-f^2) end:

`der/LambertW` := proc (der,f,x)
  LambertW(f)/(1 + LambertW(f))*der(f,x)/f
end:

`der/AiryAi` := proc(der,n,f,x) 
  if nargs = 3 then AiryAi(1,n)*der(n,f) 
  elif n = 1 then AiryAi(f)*f*der(f,x)
  elif pd(n,x) = 0 then AiryAi(n + 1, f)*der(f,x)
  else 'der'(AiryAi(n,f),x)
  fi 
end:

`der/AiryBi` := proc(der,n,f,x) 
  if nargs = 3 then AiryBi(1,n)*der(n,f) 
  elif n = 1 then AiryBi(f)*f*der(f,x)
  elif pd(n,x) = 0 then AiryBi(n + 1, f)*der(f,x)
  else 'der'(AiryBi(n,f),x)
  fi 
end:

`der/RootOf` := proc(der,f,x) 
  if has(f,x) then ERROR(`Sorry, this version of Jets cannot handle`) 
  else 0
  fi 
end:

# Printing partial derivatives

`print/pd` := proc (q,x) 'Diff'(q,`count//seq`(x)) end: 

# Diff is mapped to pd

unprotect(Diff):

Diff := proc(f) 
  if nargs = 1 then
    'Diff(f)' # Maple procedures may use Diff for other purposes
  else pd(f,convert([op(2..nargs, [args])], `*`))
  fi 
end:

#
#   A s s i g n i n g   p a r t i a l   d e r i v a t i v e s 
#

# Values assigned to partial derivatives are stored in a table.

`pd/tab` := table([]):

# Extracting values from the pd table:
# `pd//tab`(f,p) returns the value of pd(f,p).
# If ambiguous, chooses that of minimal size

`pd//tab` := proc (f,p)
  option remember; 
  local el,el1,e,ans,m,q,ql,rt,lb; 
  global `pd/tab`,`dep/tab`; 
  if type (f,'dep') and ars(p) minus `dep/tab`[f] <> {} then RETURN(0) fi;
  lb := `PD:`; rt := `report/tab`[pd];
  if assigned(`pd/tab`[f]) then
    if assigned(`pd/tab`[f][p]) then RETURN(`pd/tab`[f][p]) fi;
    el := op(2,op(`pd/tab`)[f]); # list of already assigned derivatives
    el := map(proc(e,p) p/op(1,e) = op(2,e) end, el, p); # reciprocals
    el := select(proc(e) type (op(1,e),'count') end, el); # select counts 
      if el = [] then RETURN('pd'(f,p)) fi; # if no counts at all
    el1 := select(proc(e) not type (op(1,e),{`*`,`^`}) end, el); # 1st order 
    if el1 <> [] then
      if select(type, el1, anything='numeric') <> [] then ans := 0
      else
        if rt > 3 then report(lb,[`extending table 1 step: `, nops(el1)]) fi;
        el1 := map(proc(e) Simpl(eval(pd(op(2,e),op(1,e)))) end, el1); 
        if nops(el1) > 1 then
          el1 := sizesort(el1,size);
          ans := op(1,el1); # the smallest size derivative
        else
          ans := el1[1]
        fi
      fi;
      if rt > 3 then report(lb,[`storing a value for`, 'pd'(f,p)]) fi;
      `put/1`('pd'(f,p), ans);
      RETURN (ans)
    else # no 1st order counts
      if select(type, el, anything='numeric') <> [] then
        ans := 0; `put/1`('pd'(f,p), ans); RETURN (ans)
      else
        el := map(proc(e,p) [op(e),`count/length`(op(1,e))] end, el);
        el := sort(el, proc(e1,e2) evalb(op(3,e1) < op(3,e2)) end);
        m := op(3,el[1]); # length of the shortest count
        el := select(proc(e,m) evalb(op(3,e) = m) end, el, m); 
        for e in el do # running through lowest (= m-th) order derivatives
          ql := `pd//tab/1`(op(1,e)); # list of indeterminates
          for q in ql do ans := pd(op(2,e),q);
            if rt > 3 then report(lb,[`storing `, 'pd'(f,p/op(1,e)*q)]) fi;
            `put/1`('pd'(f,p/op(1,e)*q), ans)
          od
        od;
        RETURN(`pd//tab`(f,p))
      fi
    fi 
  fi;
  'pd'(f,p)
end:

`pd//tab/1` := proc(q) # count -> list of indeterminates
  if type (q,`*`) then 
    map(proc(z) if type (z,`^`) then op(1,z) else z fi end, [op(q)]);
  elif type (q,`^`) then [op(1,q)]
  else [q]
  fi
end:

# put assigns values to pd's via `pd/tab` or `dep/tab`

put := proc()
  local e;
  if type ([args], 'list'(`=`)) then
    for e in args do `put/1`(op(e)) od
  else ERROR (`wrong arguments`)
  fi;
  `put/evaluate`();
  NULL
end:

`put/1` := proc(p,a)
  global `unk/s`,`unk/<</list`,`dep/tab`,`pd/tab`;
  if type (p,'name') then
    `unk/s` := map(`put/1/remove`, `unk/s`, p);
    `unk/<</list` := map(`put/1/remove`, `unk/<</list`, p);
    assign(p = a)
  elif type (p,specfunc(anything,'pd')) then
    if a = 0 and type (op(1,p),'dep') and type(op(2,p),'var') then 
      `dep/tab`[op(1,p)] := `dep/tab`[op(1,p)] minus {op(2,p)}
    else 
      `pd/tab`[op(1,p)][op(2,p)] := a
    fi
  else lprint (`ignoring unexpected input`, p = a)
  fi
end:

`put/1/remove` := proc(a,b) if a = b then NULL else a fi end:

`put/evaluate` := proc()
  local e,el,f,ft,q,qs,eq,rpt; 
  global `dep/tab`,`pd/tab`,`nonzero/s`;
# `refresh/1`(`pd//tab`);
  refresh();
  el := op(2,op(`pd/tab`));
  rpt := table([]);
  for e in el do
    f := op(1,e); ft := op(2,e);
    qs := map(proc(x) op(1,x) end, op(2,op(ft)));
    rpt[f] := table([]);
    for q in qs do eq := Simpl(eval(ft[q]));
      if type(q,'var') and eq = 0 and type (f,'dep') then
        `dep/tab`[f] := `dep/tab`[f] minus {q}
      else rpt[f][q] := eq
      fi
    od
  od;
  `pd/tab` := op(rpt);
  nonzero();
  map(
    proc(a)
      if Simpl(eval(a)) = 0 then
        ERROR(`declared nonzero became zero`, a)
      fi
    end, `nonzero/s`);
end:

# To convert the pd table into a list:

pds := proc()
  op(map(`pds/1`, op(2,op(`pd/tab`))))
end:

`pds/1` :=  proc(p)
   op(map(
     proc(e,f) 
       'pd'(f,op(1,e)) = op(2,e) 
     end, op(2,op(2,p)), op(1,p))) 
end:

# To convert the pd table into a set of expressions while clearing all
# assignments to pd's:

`clear/pds` := proc()
  local t,aux;
  global `pd/tab`;
  reduce();
  t := copy(`pd/tab`);
  `pd/tab` := table([]);
  refresh();
  aux := op(map(`pds/1`, op(2,op(t))));
  map(proc(e) op(1,e) - op(2,e) end, {aux});
end:



reduce := proc()
  local ans1,ans2;
  ans1 := `reduce/pd`();
  ans2 := `unks/assignments`();
  refresh();
  ans1,ans2 
end:

`unks/assignments` := proc()
  global `unk/tab`;
  local aux;
  aux := map(op,[entries(`unk/tab`)]);
  op(map(proc(f) if f <> eval(f) then f = eval(f) fi end, aux))
end:

`reduce/pd` := proc()
  local e,el,f,ft,p,pl,q,qs,qe,eq,rpt; 
  global `dep/tab`,`pd/tab`;
  el := op(2,op(`pd/tab`));
  rpt := table([]);
  for e in el do
    f := op(1,e); ft := op(2,e);
    pl := map(proc(x) op(1,x) end, op(2,op(ft)));
    if f = eval(f) then
      # remove by independence
      if type(f,'dep') then
        pl := select(proc(p,f) global `dep/tab`;
            evalb(vars(p) minus `dep/tab`[f] = {}) 
          end, pl, f)
      fi;
      qs := {op(pl)}; qe := {};
      # remove by pd consequence
      for p in pl do
        for q in qs do
          if type (q/p,'count') then qe := qe union {q} fi;
        od;
        qs := qs minus qe
      od
    else 
      # remove by assignment
      qs := {}; eq := eval(f)
    fi;
    # evaluate
    rpt[f] := table([]);
    for q in qs do eq := Simpl(eval(ft[q]));
      if type(q,'var') and eq = 0 and type (f,'dep') then
        `dep/tab`[f] := `dep/tab`[f] minus {q}
      else rpt[f][q] := eq
      fi
    od
  od;
  `pd/tab` := op(rpt);
  pds()
end:

# Checking still unresolved compatibility conditions

cc := proc()
  local e,el,f,ft,zl,p,pl,q,i,j,p1,q1,z,ans,sl,aux,rt,lb; 
  global `dep/tab`,`pd/tab`,`cc/s`,`cc/tab`;
  ans := NULL; 
  zl := [];
  lb := `CC:`; rt := `report/tab`[cc];
  el := op(2,op(`dep/tab`)); # list of stored dependences
  for e in el do 
    f := op(1,e); # an unknown
    ft := op(2,e); # its dependence set
    if rt > 3 then report(lb,[`dependence set:`, 'f' = f, 'ft'= ft]) fi;
    aux := NULL;
    if f <> eval(f) then # f assigned
      for p in vars(eval(f)) minus ft do
        # pd(f,p) should be zero
        aux := aux, [f, eval(f), p, 0, 1, 1] 
      od;
      zl := [op(zl), aux];
      if rt > 2 then report(lb,[f, cat(`ass/dep: `,nops(zl),` c.c.`)]) fi
    fi
  od;  
  el := op(2,op(`pd/tab`)); # list of stored partial derivatives
  for e in el do
    f := op(1,e); ft := op(2,e);
    if rt > 2 then report(lb,['f' = f]) fi;
    pl := map(proc(x) op(1,x) end, op(2,op(ft)));
    aux := NULL;
    if f <> eval(f) then # f assigned
      for p in pl do 
        # pd(f,p) should have the expected value
        aux := aux, [f, f, p, ft[p], 1, `count/length`(p)]; 
      od;
      zl := [op(zl), aux];
      if rt > 2 then report(lb,[f, cat(`ass/pd: `,nops([aux]),` c.c.`)]) fi
    else 
      if type(f,'dep') then # dependence
        for p in pl do
          if vars(p) minus `dep/tab`[f] <> {} then
              # pd(f,p) should be zero 
            if ft[p] <> 0 then
              aux := aux, [f, ft[p], 1, 0, 1, `count/length`(p)]
            fi
          fi; 
          if ft[p] <> 0 then
            for q in vars(ft[p]) minus `dep/tab`[f] do
              # pd(f,p*q) should vanish for each q from pd(f,p)
              aux := aux, [f, ft[p], q, 0, 1, `count/length`(p*q)]
            od
          fi
        od
      fi;
      zl := [op(zl), aux];
      if rt > 2 then report(lb,[f, cat(`dep/pd: `,nops([aux]),` c.c.`)]) fi;
      # cross differentiation
      aux := NULL;
      for i to nops(pl) do
        for j to i - 1 do p := op(i,pl); q := op(j,pl);
          if ft[p] <> 0 or ft[q] <> 0 then 
            p1 := `transform/count`(p/q); q1 := `transform/count`(q/p);
            if p*q1 <> q*p1 then ERROR(`this should not happen`) fi;
            aux := aux, [f, ft[p], q1, ft[q], p1, `count/length`(p*q1)] 
          fi
        od
      od;
      if rt > 2 then report(lb,[f, cat(`cross-derivatives: `,nops([aux]))]) fi;
      zl := [op(zl), aux];
    fi
  od;  
  if rt > 1 then report(lb,[cat(`total number: `,nops(zl),` c.c.`)]) fi;
  zl := [op({op(zl)} minus `cc/s`)];
  if rt > 1 then report(lb,[cat(`of them new: `,nops(zl),` c.c.`)]) fi;
  zl := select(proc(z,m) evalb(op(6,z) = m) end,
    zl, min(op(map(proc(z) op(6,z) end, zl))));
#   zl := select(
#     proc(z,zl) local z1;
#       for z1 in zl do
#         if type (op(6,z1)/op(6,z),'count') then RETURN(true) fi
#       od;
#       false
#     end, zl, zl);
  if rt > 1 then report(lb,[cat(`of them minimal: `,nops(zl),` c.c.`)]) fi;
  if rt > 1 then report(lb,[`to be computed:`, nops(zl),` c.c.`]) fi; 
  for z in zl do 
    aux := `cc/1`(op(1..5,z)); 
    if aux = 0 then `cc/s` := `cc/s` union {z} 
    else `cc/tab`[f,op(z)] := aux;
      ans := ans, aux
    fi;
  od;
  if rt > 0 then report(lb,[`number of c.c.:`, nops({ans})]) fi;
  {ans}
end:

`cc/s` := {}:

`cc/1` := proc(f,g,p,h,q)
  local ans,pt;
  global `cc/tab`;
  if assigned(`cc/tab`[f][g,p,h,q]) then
    Simpl(eval(`cc/tab`[f][g,p,h,q]));
  elif p = 1 then
    if q = 1 then Simpl(eval(g - h))
    else Simpl(eval(g - pd(h,q)))
    fi
  elif q = 1 then Simpl(eval(pd(g,p) - h))
  else Simpl(eval(pd(g,p) - pd(h,q)))
  fi
end:

`clear/cc` := proc()
  global `cc/s`,`cc/tab`;
  `cc/s` := {};
  `cc/tab` := table([]);
  NULL
end:

#
#   S i m p l i f y i n g
#

# Mathematically, f = simpl(f);
# it should be possible to test zero by simpl(f) = 0;
# Finally, simpl(f) = 0 iff numer(simpl(f)) = 0 

unprotect(normal):

simpl := proc(f) normal(f) end:

Simpl := proc(f)
# option remember, system;
  local V;
  if  hasfun(f, TD) then simpl(f)
  else 
    if nargs > 1 then V := args[2] else V := Vars(f) fi;
    V := select(proc(v,f) type(f,polynom(anything,v)) end, V, f);
#   V := V union unks(f); # obsolete
    collect(f, V, distributed, simpl)
  fi
end:

#
#   F i n d i n g   d e p e n d e n c e   s e t 
#

vars := proc(f)
# option remember;
  if type (f,'constant') then {}
  elif type (f,'name') then 
    if type (f,{`b/var`,`f/var`}) then {f}
    elif type (f,'parameter') then {}
    elif type (f,'dep') then select (type,`dep/tab`[f],'var')   
    else ERROR (`unknown dependence`, f)
    fi
  elif type (f,{`+`,`*`,`^`}) then `union`(op(map(vars,[op(f)])))
  elif type (f,'function') then 
    if type (f, specfunc(anything,jet)) then {f}
    elif type (f, specfunc(anything,pd)) then vars(op(1,f))
    elif type (f, specfunc(anything,TD)) then `vars/TD` (op(f))
    else `union`(op(map(vars,[op(f)])))
    fi
  else ERROR (`unexpected object`, f) 
  fi
end:

`vars/TD` := proc (f,x) 
  option remember;
  if type (x,'name') then
    vars(f) union `union`(op(map(`vars/TD/1`,vars(f),x)))
  else `vars/TD`(f,`count/r`(x)) union
    `union`(op(map(`vars/TD/1`,`vars/TD`(f,`count/r`(x)), `count/f`(x))))
  fi
end:

`vars/TD/1` := proc (q,x) 
  option remember;
  vars(evalTD(TD(q,x))) 
end:

#
#   J e t s 
#

jet := proc (u::`f/var`,x::`b/count`)
  option remember;
  local y, ans;
  if op(4,op(jet)) = NULL then 'jet'(u,sort(x,`b/var/list`))
  else 
    for y in `b/var/s` do 
      if type (x/y, 'count') then
        if jet(u,x/y) <> evaln(jet(u,x/y)) then
          RETURN (`simpl/jet`(evalTD(TD(jet(u,x/y),y))))
        fi
      fi 
    od;
    'jet'(u,sort(x,`b/var/list`))
  fi
end:

`simpl/jet` := op(simpl):

#
#   E q u a t i o n s
#

equations := proc ()
  global `eqn/list`;
  if not type ([args], 'list'(`=`)) then
    ERROR (`arguments not of type '='`)
  fi;
  `eqn/list` := map (
    proc (e)
      if not type (op(1,e), `j/var`) then 
         ERROR (`not a jet variable on lhs`, op(1,e))
      else (op(op(1,e))) = op(2,e)
      fi
    end, [args]);
  `eqn/list` := 
  map(
    proc(e)
      (op(1,e)) = simpl(eval(op(2,e)))
    end, `eqn/list`);
  refresh (); 
  op(map(proc(e) 'jet'(op(1,e)) = op(2,e) end, `eqn/list`));
end:

`eqn/list` := []:

unprotect(equation):
equation := op(equations):

#
#   R e f r e s h i n g
# 

refresh := proc()
  map (`refresh/1`, `refresh/list`);
  op(map(proc(e) assign('jet'(op(1,e)) = simpl(eval(op(2,e)))) end, 
    `eqn/list`));
end:

`refresh/1` := proc(f) assign(f=subsop(4=NULL,op(f))) end:

`refresh/list` := [jet, Simpl, `pd//tab`,
  `vars/TD`,`vars/TD/1`,
  `pd/TD`,`pd/TD/1`,
  `pars/TD`,`pars/TD/1`,
  `unks/TD`,`unks/TD/1`,
  `Vars/TD`,`Vars/TD/1`]:

remembertable := proc (f) op(4,op(f)) end:


# Symmetries

symmetries := proc ()
  local Q; global `eqn/list`;
  Q := table([args]);
  op (map (proc (e,Q) local lhs,rhs;
    lhs := `dummy/j`(op(1,e)); rhs := op(2,e);
    `symm/1`(lhs,Q) - convert (map (proc (q,rhs,Q) 
      `symm/1`(q,Q) * pd(rhs,q)
    end, [op(vars (rhs) minus `b/var/s`)], rhs, Q), `+`)
  end, `eqn/list`, Q))
end:

`symm/1` := proc (q,Q) 
  if type (q,`f/var`) then Q[q]
  else eval(subsop(0 = TD, 1 = Q[op(1,q)], q))
  fi 
end:

# Universal linearization

lin := proc (f)
  local Q; 
  Q := table([args[2..nargs]]);
  convert (map (proc (q,f,Q) `symm/1`(q,Q)*pd(f,q)
    end, [op(vars (f) minus `b/var/s`)], f, Q), `+`)
end:

# Jacobi bracket

Jacobi := proc (fl,gl)
  local i,n;
  if not type (fl,'list') then ERROR(`invalid argument`, fl) fi;
  if not type (gl,'list') then ERROR(`invalid argument`, gl) fi;
  n := nops(fl);
  if n <> nops(gl) then ERROR(n <> nops(gl)) fi;
  [seq(`Jacobi/1`(fl,gl[i]) - `Jacobi/1`(gl,fl[i]), i = 1..n)]
end:

`Jacobi/1` := proc(fl,g)
  convert(map(
    proc(q,fl,g) 
      local k; global `f/var/list`;
      if type (q,`f/var`) then member(q,`f/var/list`,k); fl[k]*pd(g,q)
      else member (op(1,q),`f/var/list`,k); TD(fl[k],op(2,q))*pd(g,q)
      fi
    end, [op(vars(g) minus `b/var/s`)], fl, g), `+`)
end:

# Conservation laws

laws := proc ()
  local k,neqns,e,lhs,rhs,aux,i,q,P; global `eqn/list`;
  P := table([args]); aux := table ([]); neqns := nops(`eqn/list`);
  for k to `f/dim` do aux[op(k,`f/var/s`)] := 0 od;
  for k to neqns do
    e := `eqn/list`[k]; lhs := `dummy/j`(op(1,e)); rhs := op(2,e);
    aux[op(1,lhs)] := aux[op(1,lhs)]
      + `count/sgn`(op(2,lhs)) * TD(P[k],op(2,lhs));
    for q in (vars (rhs) minus `b/var/s`) do
      if type (q, `f/var`) then aux[q] := aux[q] - pd(rhs,q)*P[k]
      else aux[op(1,q)] := aux[op(1,q)]
        - `count/sgn`(op(2,q)) * TD(pd(rhs,q)*P[k],op(2,q))
      fi
    od
  od;
  seq(aux[op(i,`f/var/list`)], i = 1..`f/dim`)
end:

# Zero curvature representations

zcr := proc ()
  local Z,neqns,k,e,lhs,rhs,aux,x,y,q;
  global `eqn/list`;
  if `b/dim` <> 2 then ERROR (`only two-dimensional base allowed`) fi;
  neqns := nops(`eqn/list`); Z := table([args]); aux := table ([]);
  for k to `f/dim` do aux[op(k,`f/var/list`)] := 0 od;
  for k to neqns do
    e := `eqn/list`[k]; lhs := `dummy/j`(op(1,e)); rhs := op(2,e);
    aux[op(1,lhs)] := aux[op(1,lhs)]
      + `count/sgn`(op(2,lhs))*`zc/TD`(op(Z[k]),op(2,lhs),Z);
    for q in (vars (rhs) minus `b/var/s`) do
      if type (q, `f/var`) then aux[q] := aux[q] - pd(rhs,q)*Z[k]
      else aux[op(1,q)] := aux[op(1,q)] + (`count/sgn`(op(2,q))
        *`zc/TD`(evalm(-pd(rhs,q)*op(Z[k])),op(2,q),Z))
      fi
    od
  od;
  x := op(1,`b/var/list`); y := op(2,`b/var/list`);
  evalm(TD(Z[x],y) - TD(Z[y],x) + Z[x]&*Z[y] - Z[y]&*Z[x]),
    seq(evalm(aux[op(k,`f/var/list`)]), k = 1..`f/dim`);
end:

`zc/TD` := proc (f,x,Z) 
  if type (x,`b/var`) then `zc/TD/1`(f,x,Z) 
  elif type (x,{`*`,`^`}) then
    `zc/TD`(evalm(`zc/TD/1`(f,`count/f`(x),Z)), `count/r`(x), Z)
  else ERROR (`invalid count`, x)
  fi
end:

`zc/TD/1` := proc (f,x,Z) map(TD,f,x) + f&*Z[x] - Z[x]&*f end:

zero_curvature := op(zcr):

# Pseudosymmetries

pseudosymmetries := proc ()
  local Q;
  global `eqn/list`;
  Q := table([args]);
  op (map (proc (e,Q) local lhs,rhs;
    lhs := `dummy/j`(op(1,e)); rhs := op(2,e);
    evalm(`psymm/1`(lhs,Q) - convert (map (proc (q,rhs,Q) 
      `psymm/1`(q,Q) * pd(rhs,q)
    end, [op(vars (rhs) minus `b/var/s`)], rhs, Q), `+`))
  end, `eqn/list`, Q))
end:

`psymm/1` := proc (q,Q) 
  if type (q,`f/var`) then Q[q]
  else `ps/TD`(Q[op(1,q)], op(2,q), Q)
  fi 
end:

`ps/TD` := proc (f,x,Q)
  if type (x,`b/var`) then `ps/TD/1`(f,x,Q) 
  elif type (x,{`*`,`^`}) then
    `ps/TD`(evalm(`ps/TD/1`(f,`count/f`(x),Q)), `count/r`(x), Q)
  else ERROR (`invalid count`, x)
  fi
end:

`ps/TD/1` := proc (f,x,Q) map(TD,f,x) - Q[x]&*f end:

# Converting jet to TD

`convert/TD` := proc (f)
  local qs; 
  qs := select(type,{args},`=`);
  if f = {} then
    op(map(
      proc(e,qs)
        `convert/TD/1`('jet'(op(1,e)) - op(2,e), qs)
      end, `eqn/list`, qs))
  else `convert/TD/1`(f,qs)
  fi
end:
 
`convert/TD/1` := proc(f,qs)
  if type (f,'constant') then f
  elif type (f,'name') then
    if type (f,`f/var`) then eval(subs(qs,f))
    else f
    fi
  elif type (f,{`+`,`*`,`^`}) then map (procname, f, qs)
  elif type (f,'function') then 
    if type (f,`j/var`) then
      eval(subsop (0 = TD, 1 = subs(qs,op(1,f)), f))
    elif type (f, specfunc(anything,pd)) then f
    elif type (f, specfunc(anything,TD)) then f
    else map (procname, f, qs)
    fi
  else ERROR (`unexpected object`, f)
  fi
end:

# Converting pd to diff

`convert/diff` := proc(f)
  local es;
  es := {args[2..nargs]};
  `convert/diff/1`(f,es);
end:

`convert/diff/1` := proc(f,es)
  local qs,f1;
  if type (f,'constant') then f
  elif type (f,'name') then
    if type (f,`f/var`) then eval(subs(es,f))
    else qs := ars(f);
      if qs <> {} then f(op(eval(subs(es,qs))))
      else f
      fi
    fi
  elif type (f,{`+`,`*`,`^`}) then map (procname, f, es)
  elif type (f,'function') then 
    if type (f,`j/var`) then eval(subs(es,f))
    elif type (f, specfunc(anything,pd)) then f1 := op(1,f); qs := ars(f1); 
      diff(f1(op(eval(subs(es,qs)))),`count//seq`(eval(subs(es,op(2,f))))) 
    elif type (f, specfunc(anything,TD)) then 
      ERROR(`unevaluated total derivative`)
    else map (procname, f, es)
    fi
  else ERROR (`unexpected object`, f)
  fi
end:

# Declaring unknowns

unks := proc(a)
  if type (a,{'constant','ar'}) then {}
  elif type (a,'name') then {a}
  elif type (a,{`+`,`*`,`^`,'set'}) then `union`(op(map(unks,[op(a)])))
  elif type (a,'function') then 
    if type (a,specfunc(anything,pd)) then {op(1,a)}
    elif type (a,specfunc(anything,TD)) then `unks/TD`(op(a))
    else `union`(op(map(unks,[op(a)])))
    fi
  else ERROR (`unexpected object`, a) 
  fi
end:

`unks/TD` := proc(f,x)
  option remember;
  if type (x,'name') then
    unks(f) union `union`(op(map(`unks/TD/1`,vars(f),x)))
  else `unks/TD`(f,`count/r`(x)) union
    `union`(op(map(`unks/TD/1`,`vars/TD`(f,`count/r`(x)), `count/f`(x))))
  fi
end:

`unks/TD/1` := proc (q,x) 
  option remember;
  evalTD(unks(TD(q,x))) 
end:


pars := proc(a)
  if type (a,{'constant','var'}) then {}
  elif type (a,'parameter') then {a}
  elif type (a,'name') then
    if type (a,'dep') then select (type,`dep/tab`[a],'parameter')
    else ERROR (`unknown dependence`, a)
    fi
  elif type (a,{`+`,`*`,`^`,'set'}) then `union`(op(map(unks,[op(a)])))
  elif type (a,'function') then 
    if type (a,specfunc(anything,pd)) then pars(op(1,a))
    elif type (a,specfunc(anything,TD)) then `pars/TD`(op(a))
    else `union`(op(map(pars,[op(a)])))
    fi
  else ERROR (`unexpected object`, a) 
  fi
end:

`pars/TD` := proc(f,x)
  option remember;
  if type (x,'name') then
    pars(f) union `union`(op(map(`pars/TD/1`,vars(f),x)))
  else `pars/TD`(f,`count/r`(x)) union
    `union`(op(map(`pars/TD/1`,`vars/TD`(f,`count/r`(x)), `count/f`(x))))
  fi
end:

`pars/TD/1` := proc (q,x) 
  option remember;
  evalTD (pars(TD(q,x))) 
end:



ars := proc(a) vars(a) union pars(a) end:





run := proc()
  `run/l`(op(map(`run/1`,[args])))
end:

`run/1` := proc(a)  # applies run/l to entries of lists, sets, and matrices
  if type (a,{'list','set'}) then op(map(`run/1`,a))
  elif type (a,'matrix') then
    if type (a,'name') then
      op(map(proc(x) op(2,x) end, op(3,op(a))))
    else
      op(map(proc(x) op(2,x) end, op(3,a)))
    fi
  else a
  fi
end:

`run/l` := proc()
  local as,eqs,aux,i,imax,res,t,rt,lb;
  global `run/time`,`run/bytes`, putsize, ressize, runtransformations;
  if `unk/<</list` = [] then
    ERROR (`please set unknowns(name1, name2, ...)`) 
  fi;
  clear(cc,derive);
  `run/time` := time();
  `run/bytes` := kernelopts(bytesalloc);
  lb := `RUN:`; rt := `report/tab`[run];
  do i := 0;
    if rt > 0 then report(lb,`Compatibility conditions ...`) fi;
    as := cc();
    # as = the lowest compatibility conditions
    as := select(proc(a) evalb(a <> 0) end, as);
    if rt > 1 then report(lb,[`c.c.: `, op(sort(map(size,[op(as)])))]) fi;
#   as := map(derive, as); # derive differential consequences of cc
#   if rt > 1 then
#     report(lb,[`d.c.c.: `, op(sort(map(size,[op(as)])))])
#   fi;
    if as <> {} then 
      if runtransformations <> {} then
        for t in runtransformations do
          as := as union map(Simpl@t,as)
        od;
        as := select(proc(a) evalb(a <> 0) end, as);
        if rt > 1 then
          report(lb,[`transformed d.c.c.: `, op(sort(map(size,[op(as)])))]);
        fi
      fi
    fi;
    if rt > 3 then report(lb,[`all c.c.: `], op(as)) fi;
    aux := {derive(args)};
    aux := select(proc(a) evalb(a <> 0) end, aux); 
    if rt > 1 then report(lb,[`derived: `, op(sort(map(size,[op(aux)])))]) fi;
    if runtransformations <> {} then
      for t in runtransformations do
        aux := aux union map(Simpl@t,aux)
      od;
      aux := select(proc(a) evalb(a <> 0) end, aux); 
      if rt > 1 then
        report(lb,[`transformed derived: `, op(sort(map(size,[op(aux)])))]);
        if rt > 3 then report(lb,[`transformed c.c.: `], op(as)) fi;
      fi
    fi;
    if rt > 3 then report(lb,[`all derived: `], op(aux)) fi;
    as := as union aux;
    if as = {} or as = {0} then tprint(`Success!`);
      RETURN(op(as))
    fi;
    aux := `size/*/<`(as, ressize);
    if rt > 1 then
      report(lb,[`to resolve: `, op(sort(map(size,[op(aux)])))])
    fi;
    if rt > 4 then
      report(lb,[`to resolve: `, op(aux)])
    fi;
    if aux = {} then ERROR(`ressize too low`) fi;
    res := resolve(op(aux));
    if res = FAIL then RETURN (FAIL)
    else eqs := {res};  # solved
      if rt > 1 then report(lb,[`resolved:`, op(sort(map(size,[op(eqs)])))]) fi;
      if rt > 4 then report(lb,[`resolved:`, op(eqs)]) fi
    fi;
    aux := `size/*/<`(eqs, putsize);
    if rt > 1 then report(lb,[`selected:`, op(sort(map(size,[op(eqs)])))]) fi;
    if aux = {} then ERROR(`putsize too low`) fi;
    `run/put`(op(aux));
    if Bytes() > Blimit then reduce() fi
  od
end:

`size/*/<` := proc(as,upb) 
  local aux,bs,ans,i,m,n;
  n := 1;
  ans := {};
  aux := sort([op(map(size, as))]);
  for m in aux do
    bs := select(`size/=`, as, m);
    for i to nops(bs) do
      n := n*m;
      if n > upb then RETURN(ans)
      else ans := ans union {op(i,bs)}
      fi      
    od
  od;
  ans
end:

`size/=` := proc(a,upb) evalb(size(a) = upb) end:
    
runtransformations := {}:

Blimit := 25000:

`run/put` := proc()
  put(args);
  tprint(`Put: `); map(print, [args]);
  if `storing/b` then store(`store/file`) fi
end:


pds := proc()
  op(map(`pds/1`, op(2,op(`pd/tab`))))
end:

`pds/1` :=  proc(p)
   op(map(
     proc(e,f) 
       'pd'(f,op(1,e)) = op(2,e) 
     end, op(2,op(2,p)), op(1,p))) 
end:

`store/pds` := proc()
  global `pd/tab`;
  local p,el,e,f,b; 
  reduce(); b := false;
  for p in op(2,op(`pd/tab`)) do
    el := op(2,op(2,p));
    f := op(1,p);
    for e in el do
      if b then lprint(`, `) else b := true fi;
      lprint('pd'(f,op(1,e)) = op(2,e))
    od
  od
end:

store := proc(file)
  print(cat(`storing in `, file));
  if nargs > 0 then writeto (file) else writeto(terminal) fi;
  lprint('assign'({`unks/assignments`()}));
  lprint(`; `);
  lprint('dependence'(dependence()));
  lprint(`; `);
  lprint(`put(`);
  `store/pds`();
  lprint(`); `);
  lprint('nonzero'(op(nonzero())));
  lprint(`; `);
  writeto (terminal)
end:

Bytes := proc() floor(kernelopts(bytesalloc)/1024) end:

storing := proc(file)
  global `storing/b`,`store/file`;
  if nargs > 0 then `storing/b` := true; `store/file` := file;
    lprint(cat(`Storing intermediate results in `, `store/file`));
  else `storing/b` := false;
    lprint(`No storing`);
  fi
end:

`storing/b` := false:


# ressize = the product of sizes of expressions to be resolved
# maxsize = the maximal size of result of resolve
# putsize = the product of sizes of expressions to be put

ressize := 500:
putsize := 40:
maxsize := 20:

`run/time` := time():
`run/bytes` := kernelopts(bytesalloc):


derive := proc()
  local a;
  global `derive/tab`,`derive/pd/tab`,`noderive/s`;
  for a in [args] do
    if not assigned(`derive/tab`[a,1]) then 
      `derive/tab`[a,1] := vars(a) minus `noderive/s`
    fi;
    if not assigned(`derive/pd/tab`[a,1]) then 
      `derive/pd/tab`[a,1] := a
    fi
  od;
  seq(`derive/1`(a,1), a = [args])
end:

noderives := proc()
  global `noderive/s`,`b/var/s`;
  `noderive/s` := {args} union `b/var/s`
end:

noderives():

`derive/1` := proc(a,c)
  local ds,us,ps,p,aux,t,ns,s,b,rt,lb;
  global `derive/tab`,`derive/pd/tab`;
  rt := `report/tab`[derive]; lb := `DERIVE:`;
  if rt > 3 then report(lb,[`expression:`], `derive/pd/tab`[a,c]) fi;
  ds := `derive/tab`[a,c];
  if rt > 3 then report(lb,[`variables:`, op(ds)]) fi;
  if nargs > 2 then us := args[3] intersect ds;
    if rt > 3 then report(lb,[`usable variables:`, op(us)]) fi    
  else us := ds
  fi;
  ns := us;  # just anything nonempty if us nonempty
  while ns <> {} do
    ps := `remove/vars/<`(us,us);  # top vars
    aux := [seq(p = `derive/pd`(a,c,p), p = ps)];  # [p = pd(a,p), ...]
    aux := select(proc(e) op(2,e) <> 0 end, aux);  # select pd <> 0
    ns := ps minus map(proc(e) op(1,e) end, {op(aux)});  # top, but pd = 0
    if ns <> {} then
      if rt > 3 then report (lb,[`no dependence on`, op(ns)]) fi;
      us := us minus ns;
      ds := ds minus ns;
      if rt > 3 then report(lb,[`storing for`, c, `: `, ds]) fi;
      `derive/tab`[a,c] := ds
    fi;
  od;  # all top vars now with pd <> 0
  if us = {} then if rt > 2 then report(lb,`vars exhausted`) fi;
    RETURN(Simpl(evalTD(`derive/pd/tab`[a,c])))
  fi;
  if rt > 3 then report(lb,[`top vars:`, op(ps)]) fi;
  aux := [seq([op(p),size(op(2,p))], p = aux)];  # [[p, pd(a,p), size], ...]
# aux := sort(aux, proc(t1,t2) evalb(op(3,t1) < op(3,t2)) end);  # sort by size
  s := size(`derive/pd/tab`[a,c]);
  if rt > 3 then report(lb,[`current size:`, s]) fi;
  aux := select(proc(t,s) op(3,t) < s end, aux, s);  # select < a
  if aux = [] then if rt > 3 then report(lb,`none makes less`) fi; 
    if rt > 2 then report(lb,[`derivation finished`]) fi;
    RETURN(Simpl(evalTD(`derive/pd/tab`[a,c])))
  fi;
  ns := ps minus map(proc(e) op(1,e) end, {op(aux)});  # vars failing < a
  if ns <> {} then
    if rt > 3 then report(lb,[`vars failing make less:`, op(ns)]) fi;
    us := `remove/vars/<`(us,ns) minus ns;
  fi;
  if rt > 3 then report(lb,[cat(`continuing `,nops(aux),` expression(s)`)]) fi; 
  for t in aux do
    if not assigned(`derive/tab`[a,c*op(1,t)]) then 
      `derive/tab`[a,c*op(1,t)] := ds
    fi
  od;
  seq(`derive/1`(a, c*op(1,t), us), t = aux)
end:

`remove/vars/<` := proc(qs,ps)
  local p,ms;
  if qs = {} then {} 
  else ms := qs;
    for p in ps do ms := ms minus select(`vars/<`,ms,p) od;
    ms
  fi
end:

`vars/<` := proc(q1,q2)
  if type (q2,'name') then false
  elif type (q1,'name') then evalb(q1=op(1,q2))
  else evalb (op(1,q1)=op(1,q2) and type (op(2,q2)/op(2,q1),'count'))
  fi
end:

###`vars/<` := proc(q1,q2) `vars/<<`(q1,q2) end:


`derive/pd` := proc(a,c,q)
  local ans,rt,lb;
  global `derive/pd/tab`;
  rt := `report/tab`[derive]: lb := `DERIVE:`;
  if assigned(`derive/pd/tab`[a,c*q]) then 
    ans := Simpl(evalTD(`derive/pd/tab`[a,c*q]))
  elif assigned(`derive/pd/tab`[a,c]) then
    if rt > 3 then report(lb,[`actually deriving;`, q]) fi;
    ans := Simpl(evalTD(pd(`derive/pd/tab`[a,c],q)))
  else ERROR (`this should not happen`)
  fi;
  `derive/pd/tab`[a,c*q] := ans;
  ans
end:


`derive/pd/tab` := table([]):

`clear/derive` := proc()
  global `derive/tab`,`derive/pd/tab`;
  `derive/pd/tab` := table([]);
  `derive/tab` := table([]);
  NULL 
end:


#
#  R e s o l v e
#

resolve := proc()
  local as,bs,vl,i,rt,lb;
  lb := `RESOLVE:`; rt := `report/tab`[resolve];
  as := map(numer@normal,{args}) minus {0};
  if rt > 3 then report(lb,cat(`input `, nops(as), ` eqns`), as) fi; 
  as := map(divideout, as); # remove nonzero factors
  if rt > 3 then report(lb,cat(`divideout `, nops(as), ` eqns `), as) fi; 
  bs := select(type, as, nonzero);
  if rt > 3 then report(lb,cat(`contradictory `, nops(bs), ` eqns `), bs) fi; 
  if bs <> {} then print(op(map(proc(b) b = 0 end, bs)));
    ERROR(`there are contradictory equations`)
  fi;
  vl := [op(`union`(op(map(Vars,as))))]; # present Vars 
  if vl = [] then ERROR(`no unknowns`, as) fi;
  vl := sort(vl,`Vars/<<`); # Vars in current Varordering
  vl := [seq(vl[nops(vl) - i], i = 0..nops(vl) - 1)];  # reverse 
  `resolve/lin`(as,vl)
end:

`type/nounks` := proc(a) evalb(unks(a) = {}) end:

`type/resolv` := proc(x)
  evalb(vars(a) minus `union`(op(map(vars,unks(a)))) = {})
end:


`resolve/lin` := proc(as,vl)
  local bs,v,cs,ls,ps,p,q,qs,ans,aux,rs,rt,lb;
  global maxsize;
  lb := `RESOLVE:`; rt := `report/tab`[resolve];
  bs := map(Simpl, as, vl);
  if rt > 2 then report(lb,cat(`resolving `, nops(bs),` eq.`)) fi; 
  bs := remove(proc(a) evalb(a = 0) end, bs);  # remove zero eqs.
  if rt > 2 then report(lb,cat(nops(bs), ` eq. nonzero`)) fi; 
  if bs = {} then RETURN () fi;  # no eq.
  ans := {}; rs := {}; 
  # Correction: rvl removed 12.7.2007
  for v in vl do # for v running through all Vars in reverse Varordering
    if rt > 3 then report(lb,`resolving with respect to`, v) fi; 
    bs := map(divideout, bs); # remove nonzero factors
    bs := map(Simpl, bs, vl); # Simplify
    bs := remove(proc(a) evalb(a = 0) end, bs);  # remove zero eqs.
    bs := map(reduceprod, bs);  # reduce products
    cs := select(has, bs, v);  # cs = subset of bs with v 
    if rt > 4 then report(lb,`resolving equations:`, cs) fi; 
    bs := bs minus cs;  # bs = subset without v
    ls := select(type, cs, linear(v));  # ls = subset of cs linear in v
    if rt > 4 then report(lb,`of them linear:`, ls) fi; 
    ps := select(proc(a,v) type (coeff(a,v,1),'nonzero') end, ls, v);
    if ps <> {} then                            # if solvable eqs,
      qs := map(Simpl, map(`resolve/lin/1`, ps, v), vl); # solve all ps
      if rt > 4 then report(lb,`available solutions:`, qs) fi; 
      qs := sizesort([op(qs)], size);
      q := op(1,qs);
      if rt > 4 then report(lb,`using solution:`, q) fi; 
      bs := bs union map(`resolve/subs`, cs, v, q);
      if rt > 4 then report(lb,`back substituted system:`, bs) fi; 
      ans := {v = q} union map(
        proc(a,v,q) op(1,a) = `resolve/subs`(op(2,a), v, q) end, ans, v, q)
    else 
      # try to subtract pairs of equations; not implemented yet
      rs := rs union map(proc(a,v) [a,v] end, cs, v)  # move cs to rs
    fi
  od;
  if rt > 2 then report(lb,cat(`solved `, nops(ans), ` eq.`)) fi; 
  if rt > 2 then report(lb,cat(`rejected `, nops(rs), ` eq.`)) fi; 
  if rt > 2 then report(lb,cat(`left `, nops(bs), ` eq.`)) fi; 
  ans := map(Simpl, map(eval,ans), vl);
  rs := map(proc(r,vl) [Simpl(op(1,r), vl), op(2,r)] end, rs, vl);
  rs := select(proc(r) evalb(op(1,r) <> 0) end, rs);
  aux := ans;
  ans := select(proc(a) size(a) < maxsize end, ans);
  aux := aux minus ans;
  if ans = {} then
    if aux <> {} then lprint(`There are`, nops(aux),
      `suppressed solutions of sizes:`, op(map(size,aux)))
    fi;
    map(
      proc(r) 
        if type(op(1,r), linear(op(2,r))) then 
          tprint(`linear resolving failed for`, op(2,r));
          print (coeff(op(r),1)*op(2,r) = -coeff(op(r),0))
        else tprint(`resolving failed for`, op(2,r), `nonlinear `);
          print (op(1,r))
        fi
      end, rs);
    FAIL
  else op(ans)
  fi;
end:

`resolve/lin/1` := proc(p,v) -coeff(p,v,0)/coeff(p,v,1) end:

`resolve/subs` := proc(a,v,q)
  Simpl(subs(v = q, a)) # Correction: Simpl added 9.7.2007
end:

`type/resolvable` := proc(a)
  if unks(a) <> {} and
    vars(a) minus `union`(op(map(vars,unks(a)))) = {} then false
  else true
  fi
end:



Vars := proc(a)
  global `unk/s`;
  if type (a,{'constant','ar'}) then {}
  elif type (a,'name') then
    if member(a,`unk/s`) then {a} else {} fi
  elif type (a,{`+`,`*`,`^`,`=`}) then `union`(op(map(procname, [op(a)])))
  elif type (a,'function') then 
    if type (a,specfunc(anything,pd)) then
      if member(op(1,a),`unk/s`) then {a} else {} fi
    elif type (a,specfunc(anything,TD)) then `Vars/TD`(op(a))
    else `union`(op(map(procname, [op(a)])))
    fi
  else ERROR (`unexpected object`, a) 
  fi
end:

`Vars/TD` := proc(f,x)
  option remember;
  if type (x,'name') then
      `union`(op(map(`Vars/TD/0`, vars(f), f, x)))
    union
      `union`(op(map(`Vars/TD/1`,vars(f),x)))
  else `union`(op(map(
      `Vars/TD/0`,`vars/TD`(f,`count/r`(x)),TD(f,`count/r`(x)),`count/f`(x))))
    union
      `union`(op(map(`Vars/TD/1`,`vars/TD`(f,`count/r`(x)),`count/f`(x)))) 
  fi
end:

`Vars/TD/0` := proc(q,f,x)
  if type (q,`b/var`) and q <> x then {} else Vars(pd(f,q)) fi
end:

`Vars/TD/1` := proc (q,x) 
  option remember;
  Vars(evalTD(TD(q,x))) 
end:

#
#  N o n z e r o
#

# Declaring nonzero expressions

nonzero := proc()
  local nsa,f,nsb,ans;
  global `nonzero/s`;
  if assigned(`nonzero/s`) then
    `nonzero/s` := {args} union `nonzero/s`;
    `nonzero/s` := map(numer@simpl,`nonzero/s`)
  else `nonzero/s` := map(numer@simpl,{args})
  fi;
  ans := {};
  nsb := [op(map(`nonzero/1`,`nonzero/s`))];
  while not nsb = [] do
    nsa := sizesort(nsb,`divideout/size`); 
    f := op(1,nsa); # the smallest expression in nsa
    nsb := [op(2..nops(nsa), nsa)]; # the rest
    nsb := map(divideout,nsb,{f}); # simplified
    if f <> 1 then ans := ans union {f} fi
  od;
  `nonzero/s` := ans
end:

`nonzero/s` := {}:

`nonzero/1` :=  proc(a)  # treats explicit products and powers
  if unks(a) = {} then NULL
  elif type (a,`^`) then
    if type (op(2,a), rational) and op(2,a) > 0 then procname(op(1,a))
    else a
    fi
  elif type (a,`*`) then op(map(procname,[op(a)]))
  else a
  fi
end:

# Dividing out nonzero factors.
# Nonzero is either declared nonzero or free of unknowns
# (and not equal to zero).

divideout := proc(a)   
  local ns;
  if nargs = 1 then ns := `nonzero/s` else ns := args[2] fi;
  `divideout/nonzero`(`divideout/nounks`(factor(Simpl(a))),ns) 
  # Correction: Simpl added 9.7.2004
end:

`divideout/nounks` := proc(a)  # treats explicit products and powers
  if a = 0 then 0 # Correction: 0 added 9.12.2004
  elif unks(a) = {} then 1
  elif type (a,`^`) then
    if type (op(2,a), posint) then procname(op(1,a)) else a fi
  elif type (a,`*`) then map(procname,a)
  else a
  fi
end:

`divideout/nonzero` := proc(a,ns)  # divides elements of ns out of a
  local f,g,h;
  g := normal(a);
  for f in ns do h := normal(g/f);
    while `divideout/size`(h) < `divideout/size`(g) do
      g := h; h := normal(g/f); 
    od
  od;
  if type (g,'constant') then 1 else g fi
end:

`divideout/size` := proc(x) `size/alg`(x,2) end:

`size/alg` := proc(f,m)  # a positive number
  if type (f,'constant') then 1
  elif type (f,`^`) then procname(op(1,f),m)^procname(op(2,f),m)
  elif type (f,`+`) then `+`(op(map(procname, [op(f)], m)))
  elif type (f,`*`) then `*`(op(map(procname, [op(f)], m)))
  else m
  fi
end:

# Recognizing nonzero expressions

`type/nonzero` := proc (b) evalb(divideout(numer(simpl(b))) = 1) end:

`clear/nonzero` := proc()
  local ans;
  global `nonzero/s`;
  ans := `nonzero/s`;
  `nonzero/s` := {};
  ans
end:

nonzeroes := proc()
  `clear/nonzero`();
  nonzero(args)
end:

# Reporting about the progression
# Syntax: reporting(derive = 0, resolve = 0, run = 0, cc = 0, pd = 0); 
# These are the default values. When changed to positive values,
# information will be issued about the relevant steps.

reporting := proc ()
  global reportfile,`report/tab`;
  local rlist,aux,e;
  rlist := select(type, [args], `=`); 
  aux := {args} minus {op(rlist)};
  if nops(aux) > 1 then ERROR(`wrong arguments`, op(aux))
  elif nops(aux) = 1 then reportfile := op(1,aux)
  else reportfile := terminal
  fi; print(rlist);
  for e in rlist do `report/tab`[op(1,e)] := op(2,e) od;
  lprint (cat(`Reporting to `, reportfile));
  aux := op(2,op(`report/tab`));
  print(aux)
end:

report := proc(lb,text)
  global `run/time`,`run/bytes`;
  local i,t,w; 
  appendto (reportfile);
  t := cat(`<`,floor(time() - `run/time`),`>`);
  w := cat(`<`,Bytes(),`>`);
  if type (text,'name') then lprint(lb, t, w, text) 
  else lprint(lb, t, w, op(text)) 
  fi;
  for i from 3 to nargs do print(args[i]) od;
  print();
  writeto (terminal); NULL
end:

`report/tab`[derive] := 0:
`report/tab`[resolve] := 0:
`report/tab`[run] := 0:
`report/tab`[cc] := 0:
`report/tab`[pd] := 0:

lb := NULL:

tprint := proc() lprint(cat(`<`,floor(time() - `run/time`),`>`), args) end:

#
#   O r d e r i n g s
#

`list/<<` := proc(x1,x2,xl)
  local n1,n2;
  if not member(x1,xl,n1) then ERROR (`not in the list`, x1) fi;
  if not member(x2,xl,n2) then ERROR (`not in the list`, x2) fi;
  evalb(n1 < n2)
end:

`vars/<<` := proc(q1,q2)
  local x1,x2,u1,u2,o;
  global `b/<</list`,`var/<</opt`;
  if type (q2,`b/var`) then 
    if type (q1,`b/var`) then RETURN (`list/<<`(q1,q2,`b/<</list`))
    else RETURN (false)
    fi
  elif type (q1,`b/var`) then RETURN (true)
  fi;
  if type (q2,`f/var`) then u2 := q2; x2 := 1
  elif type (q2,`j/var`) then u2 := op(1,q2); x2 := op(2,q2)
  else ERROR (`not a variable`, q2)
  fi;
  if type (q1,`f/var`) then u1 := q1; x1 := 1
  elif type (q1,`j/var`) then u1 := op(1,q1); x1 := op(2,q1)
  else ERROR (`not a variable`, q1)
  fi;
  for o in `var/<</opt` do
    if not Existing(`vars/<</`,o) then ERROR (`invalid option`, o) fi;
    if Call(`vars/<</`,o)(u1,x1,u2,x2) then RETURN (true) fi;
    if Call(`vars/<</`,o)(u2,x2,u1,x1) then RETURN (false) fi 
  od;
  false
end:

`vars/<</degree` := proc(u1,x1,u2,x2)
  evalb (`count/length`(x1) < `count/length`(x2))
end:

`vars/<</function` := proc(u1,x1,u2,x2)
  global `f/<</list`;
  evalb (`list/<<`(u1, u2, `f/<</list`))
end:

`vars/<</count` := proc(u1,x1,u2,x2)
  `vars/<</c/1`(x2/x1);
end:
 
`vars/<</c/1` := proc(x)
  local y,yl;
  global `b/<</list`;
  if x = 1 then false
  elif type (x,'name') then true
  elif type (x,`^`) then type(op(2,x),'posint')
  elif type (x,`*`) then 
    yl := select(proc(y,x) has(x,y) end, `b/<</list`, x);
    y := op(nops(yl), yl);
    evalb(has(`transform/count`(x), y))
  else ERROR (`not a count`, x)
  fi 
end:
 
`var/<</opt` := ['degree','function','count']:
 
varordering := proc()
  local aux;
  global `var/<</opt`; 
  `var/<</opt` := [args];
  aux := expand((1 + convert(`b/var/s`,`+`))^2 - 1);
  aux := map(proc(a) a/coeffs(a) end, [op(aux)]);
  aux := map(
    proc(u,aux)
      op(map(proc(x,u) 'jet'(u,x) end, aux, u))
    end, `f/var/list`, aux);
  aux := sort([op(`b/var/s`), op(`f/var/s`), op(aux)], `vars/<<`);
  op(aux)
end:

`b/<</list` := []:
`f/<</list` := []:

# bvariables := proc() global `b/<</list`; `b/<</list` := [args] end:
# fvariables := proc() global `f/<</list`; `f/<</list` := [args] end:

`Vars/<<` := proc(q1,q2)
  local x1,x2,u1,u2,o;
  global `Var/<</opt`;
  if type (q2,'name') then u2 := q2; x2 := 1
  elif type (q2,specfunc(anything,pd)) then u2 := op(1,q2); x2 := op(2,q2)
  elif type (q2,specfunc(anything,TD)) then u2 := op(1,q2); x2 := op(2,q2)
  else ERROR (`wrong argument`, q2)
  fi;
  if type (q1,'name') then u1 := q1; x1 := 1
  elif type (q1,specfunc(anything,pd)) then u1 := op(1,q1); x1 := op(2,q1)
  elif type (q1,specfunc(anything,TD)) then u1 := op(1,q1); x1 := op(2,q1)
  else ERROR (`wrong argument`, q1)
  fi;
  for o in `Var/<</opt` do
    if not Existing(`Vars/<</`,o) then ERROR (`invalid option`, o) fi;
    if Call(`Vars/<</`,o)(u1,x1,u2,x2) then RETURN (true) fi;
    if Call(`Vars/<</`,o)(u2,x2,u1,x1) then RETURN (false) fi 
  od;
  false
end:

`Vars/<</degree` := proc(u1,x1,u2,x2)
  evalb (`count/length`(x1) < `count/length`(x2))
end:

`Vars/<</function` := proc(u1,x1,u2,x2)
  global `unk/<</list`;
  evalb (`list/<<`(u1, u2, `unk/<</list`))
end:

`Vars/<</count` := proc(u1,x1,u2,x2)
  `Vars/<</c/1`(x2/x1);
end:
 
`Vars/<</c/1` := proc(x)
  local y,yl;
  if x = 1 then false
  elif type (x,'var') then true
  elif type (x,`^`) then type(op(2,x),'posint')
  elif type (x,`*`) then 
    yl := [op(vars(x))];
    yl := sort(yl,`vars/<<`);
    y := op(nops(yl), yl); 
    member(y, [op(vars(`transform/count`(x)))])
  else ERROR (`not a count`, x)
  fi 
end:

`Vars/<</reverse` := proc(u1,x1,u2,x2)
  `Vars/<</r/1`(x2/x1);
end:
 
`Vars/<</r/1` := proc(x)
  local y,yl;
  if x = 1 then false
  elif type (x,'var') then true
  elif type (x,`^`) then type(op(2,x),'posint')
  elif type (x,`*`) then 
    yl := [op(vars(x))];
    yl := sort(yl,`vars/<<`);
    y := op(1, yl);
    member(y, [op(vars(`transform/count`(x)))])
  else ERROR (`not a count`, x)
  fi 
end:

`Var/<</opt` := ['function','degree','reverse']:

Varordering := proc()
  local aux1,aux2,Aux;
  global `unk/<</list`,`Var/<</opt`; 
  if `unk/<</list` = [] then
    ERROR (`call unknowns(name1 name2, ...)`) 
  fi;
  `Var/<</opt` := [args];
  aux1 := `f/<</list`;
  if nops(aux1) > 1 then aux1 := aux1[1..2] fi;
  aux2 := `unk/<</list`;
  if nops(aux2) > 1 then aux2 := aux2[1..2] fi;
  Aux := expand((1 + convert(aux1,`+`))^2 - 1);
  Aux := map(proc(a) a/coeffs(a) end, [op(Aux)]);
  Aux := map(
    proc(u,Aux)
      op(map(proc(x,u) 'pd'(u,x) end, Aux, u))
    end, aux2, Aux);
  Aux := sort([op(aux2), op(Aux)], `Vars/<<`);
  op(Aux)
end:


unknowns := proc()
  global `unk/<</list`,`unk/s`,`unk/tab`; 
  `unk/s` := {args}; 
  `unk/<</list` := [args];
  `unk/tab` := table([args]);
  op(`unk/<</list`)
end:

`unk/<</list` := []:
`unk/s` := {}:
`unk/tab` := table([]):

`type/Var` := {'name',specfunc(anything,pd)}:

#
#   P r o c e d u r e s   t o   a s s i s t   c o m p u t a t i o n s
#

# From Z, select expressions containing unknowns from A.

unksselect := proc(Z,A)
  select(proc(z,A) unks(z) minus A = {} end, Z, A)
end:

# Compute coefficients of multivariate polynomials
# mcoeff (expr, x1 = n1, x2 = n2, ...);

mcoeff := proc(a)
  local i,b;
  collect(a, map(proc(x) op(1,x) end, [args[2..nargs]]));
  b := a;
  for i from 2 to nargs do
    b := coeff(b,op(args[i]))
  od
end:

#
#   C o m p u t a t i o n   o f   c o v e r i n g s
#

nonlocal := proc()
  global `name/tab`;
  local a,aux;
  aux := select (type,{args},name);
  if aux <> {args} then ERROR(`not a name`, op({args} minus aux)) fi;
  aux := select(
    proc(a)
      type (a,'dep')
      or type (a,{`b/var`,`f/var`,'constant'})
      or (type (`name/tab`[a],'set')
        and `name/tab`[a] minus {'parameter','nonlocal'} <> {})
    end, {args});
  if aux <> {} then ERROR (`name(s) already used`, op(aux)) fi;
  for a in [args] do 
    if type (`name/tab`[a],'set') then
      `name/tab`[a] := `name/tab`[a] union {'nonlocal','parameter'}
    else `name/tab`[a] := {'nonlocal','parameter'}
    fi
  od;
  registered('nonlocal')
end:

`clear/nonlocal` := proc()
  local a,aux;
  global `name/tab`;
  aux := {registered('nonlocal')};
  for a in aux do
    `name/tab`[a] := `name/tab`[a] minus {'nonlocal'} 
  od;
  op(aux)
end:

nonlocals := proc()
  `clear/nonlocal`();
  nonlocal(args)
end:


`type/nonlocal` := proc(x) 
  global `nonlocal/s`;
  evalb(type (x,'name') and type (`name/tab`[x],'set') 
    and member ('nonlocal',`name/tab`[x])) end:





vectorfield := proc()
  global `name/tab`;
  local a,aux;
  aux := select (type,{args},name);
  if aux <> {args} then ERROR(`not a name`, op({args} minus aux)) fi;
  aux := select(
    proc(a)
      type (a,{`b/var`,`f/var`,'constant'})
      or (type (`name/tab`[a],'set')
        and `name/tab`[a] minus {'vectorfield','tail'} <> {})
    end, {args});
  if aux <> {} then ERROR (`name(s) already used`, op(aux)) fi;
  for a in [args] do 
    if type (`name/tab`[a],'set') then
      `name/tab`[a] := `name/tab`[a] union {'vectorfield'}
    else `name/tab`[a] := {'vectorfield'}
    fi
  od;
  registered('vectorfield')
end:

`clear/vectorfield` := proc()
  local a,aux;
  global `name/tab`;
  aux := {registered('vectorfield')};
  for a in aux do
    `name/tab`[a] := `name/tab`[a] minus {'vectorfield'} 
  od;
  op(aux)
end:

vectorfields := proc()
  `clear/vestorfield`();
  vectorfield(args)
end:


`type/vectorfield/pd` := proc(a) 
  evalb(type (a,indexed) and op(0,a) = 'pd' and type (op(1,a),'ar'))
end:

`type/vectorfield/TD` := proc(a) 
  evalb(type (a,indexed) and op(0,a) = 'TD' and type (op(1,a),`b/var`))
end:

`type/vectorfield/c` := specfunc(anything,'comm'):

`type/vectorfield` := proc(a)
  local b;
  global `name/tab`;
  if a = 0 then true
  elif type (a,`+`) then
    for b in a do
      if not type (b,'vectorfield') then RETURN(false) fi
    od; true
  elif type (a,`*`) then
    b := select(type,a,'vectorfield');
    if b = 1 then RETURN (false) 
    elif type (b,`*`) then RETURN (false)
    else true
    fi;
  elif type (a,`^`) then false
  elif type (a,specfunc(anything,{pd,TD})) then
    type(op(1,a),'vectorfield') 
  elif type (a,{`vectorfield/pd`,`vectorfield/TD`}) then
    true
  elif type (a,'name') and type (`name/tab`[a],'set') then
    member('vectorfield',`name/tab`[a]) 
  else type (a,`vectorfield/c`) 
  fi
end:



tail := proc()
  global `name/tab`;
  local a,aux;
  aux := select (type,{args},name);
  if aux <> {args} then ERROR(`not a name`, op({args} minus aux)) fi;
  aux := select(
    proc(a) type (a,{`b/var`,`f/var`,'constant'})
      or (type (`name/tab`[a],'set')
        and `name/tab`[a] minus {'tail','vectorfield'} <> {})
    end, {args});
  if aux <> {} then ERROR (`name(s) already used`, op(aux)) fi;
  for a in [args] do 
    if type (`name/tab`[a],'set') then
      `name/tab`[a] := `name/tab`[a] union {'vectorfield','tail'}
    else `name/tab`[a] := {'vectorfield','tail'}
    fi
  od;
  registered('tail')
end:

`clear/tail` := proc()
  local a,aux;
  global `name/tab`;
  aux := {registered('tail')};
  for a in aux do
    `name/tab`[a] := `name/tab`[a] minus {'tail'} 
  od;
  op(aux)
end:

tails := proc()
  `clear/tail`();
  tail(args)
end:


`type/tail` := proc(a)
  local b;
  if a = 0 then true
  elif type (a,`+`) then
    for b in a do
      if not type (b,`tail`) then RETURN(false) fi
    od; true
  elif type (a,`*`) then
    b := select(type,a,'vectorfield');
    if b = 1 then RETURN (false) 
    elif type (b,`*`) then RETURN (false)
    else type (b,`tail`)
    fi;
  elif type (a,`^`) then false
  elif type (a,specfunc(anything,{pd,TD})) then
    type(op(1,a),`tail`) 
  elif type (a,`vectorfield/pd`) then type (op(1,a),'nonlocal')
  elif type (a,`vectorfield/TD`) then false
  elif type (a,'name') and type (`name/tab`[a],'set') then
    member ('tail',`name/tab`[a])
  elif type (a,`vectorfield/c`) then 
    type (op(1,a),`tail`) and type (op(2,a),`tail`)
  else false
  fi
end:

unprotect(apply):

apply := proc(x,f) 
  local s;
  if x = 0 then 0
  elif type (x,`+`) then map (procname, x, f)  
  elif type (x,`*`) then  
    s := select(type,x,'vectorfield');
    if s = 1 then ERROR(`no vectorfield`, x) 
    elif type(s,`*`) then ERROR(`too many vectorfields`, x) 
    else RETURN(x/s*procname(s,f))
    fi
  elif type (x,`vectorfield/pd`) then pd(f,op(x))
  elif type (x,`vectorfield/TD`) then TD(f,op(x))
  elif type (x,`vectorfield/c`) then 
    apply(op(1,x), apply(op(2,x),f))
     - apply(op(2,x), apply(op(1,x),f))
  elif type (x,'name') then
    if type (x,`vectorfield`) then `apply/~`(f,x)
    else ERROR (`not a vectorfield`, x)
    fi
  else ERROR (`a vectorfield of unknown type`, f)
  fi
end:


`pd/indexed/pd` := proc(q,p) 0 end:

`pd/indexed/TD` := proc(x,p) 
  if type (p,'nonlocal') then 0
  else 'apply'(pd[p],TD[x])
  fi
end:

`TD/indexed/pd` := proc(q,x) 0 end:

`TD/indexed/TD` := proc(x,y) 
  'apply'(TD[y],TD[x])
end:

`apply/~` := proc(f,x) 
  if type (x,'tail') and type (f,'dep') then
    if ars(f) intersect `nonlocal/s` = {} then
      RETURN (0)
    fi
  fi;
  if type (f,'constant') then 0
  elif type (f,'name') then 
    if type (f,'var') then 
      if type (x,'tail') then 0 
      else 'apply'(x,f)
      fi
    elif type (f,'dep') then
      if `dep/tab`[f] = {} then 0
      elif type (x,'tail') and ars(f) intersect `nonlocal/s` = {} then 0
      else 'apply'(x,f)
      fi
    elif type (f,{`vectorfield/TD`,`vectorfield/pd`}) then
      if type (x,'tail') then 0 
      else 'apply'(x,f)
      fi 
    else 'apply'(x,f)
    fi
  elif type (f,`+`) then map (procname, f, x)  
  elif type (f,`*`) then `der/*` (procname, f, x)
  elif type (f,`^`) then `der/^` (procname, op(f), x)
  elif type (f,'function') then 
    if op(0,f) = 'apply' then 'apply'(x,f)
    elif type (f, specfunc(anything,{pd,TD})) then 'apply'(x,f)
    elif type (f, specfunc(anything,'jet')) then 
      if type (x,'tail') then 0 
      else 'apply'(x,f)
      fi
    elif Existing(`der/`,op(0,f)) then
      Call(`der/`,op(0,f))(procname,op(f),x)
    else ERROR (`unknown function`, op(0,f))
    fi
  else ERROR (`unknown object`, f)
  fi
end:

`der/apply` := proc(pd,f,p) 'pd'(f,p) end:

# Commutator

comm := proc(x,y)
  local s;
  if x = y or x = 0 or y = 0 then RETURN (0)
  elif type (x,`+`) then RETURN (map(procname,x,y))
  elif type (y,`+`) then RETURN (-map(procname,y,x))
  elif type (x,`*`) then
    s := select(type,x,'vectorfield');
    if s = 1 then ERROR (`no vectorfield in a product`, x) 
    elif type (s,`*`) then
      ERROR (`too many vectorfields in a product`, x) 
    else RETURN(x/s*procname(s,y) - apply(y,x/s)*s)
    fi;
  elif type (y,`*`) then
    s := select(type,y,'vectorfield');
    if s = 1 then ERROR (`no vectorfield in a product`, y) 
    elif type(s,`*`) then
      ERROR(`too many vectorfields in a product`, y) 
    else RETURN(y/s*procname(x,s) + apply(x,y/s)*s)
    fi
  elif type (x,`vectorfield/TD`) then RETURN (`comm/TD`(x,y))
  elif type (y,`vectorfield/TD`) then RETURN (-`comm/TD`(y,x))
  elif type (x,`vectorfield/pd`) then RETURN (apply(x,y))
  elif type (y,`vectorfield/pd`) then RETURN (-apply(y,x))
  fi;
  if `comm/<<`(y,x) then -comm(y,x)
  elif type (y,`vectorfield/c`) and `comm/<<`(x,op(1,y)) then 
    comm(op(1,y), comm(x,op(2,y))) - comm(op(2,y), comm(x,op(1,y)))
  else 'comm'(x,y)
  fi
end:

`comm/TD` := proc(x,y)
  if type (y,`vectorfield/TD`) then RETURN (0)
  elif type (y,'tail') then apply(x,y)
  else 'comm'(x,y)
  fi
end:

`comm/<<` := proc(x,y)
  local sx,sy,lx,ly;
  sx := `comm//seq`(x); sy := `comm//seq`(y);
  lx := nops([sx]); ly := nops([sy]);
  if lx = ly then evalb (addressof(x) < addressof(y))
  else evalb (lx < ly)
  fi 
end:

`comm//seq` := proc(x)
  if type (x,`vectorfield/c`) then op(map(`comm//seq`,x))
  else x
  fi
end:

`der/comm`  := proc (pd,f,g,p) 
  if nargs = 4 then comm(pd(f,p),g) + comm(f,pd(g,p))
  else ERROR (`wrong number of arguments`)
  fi
end:


# Evolutionary differentiation

eapply := proc(v,f)
  convert(map(
    proc(q,v,f) 
      if type (q,`f/var`) then coeff(v,pd[q])*pd(f,q)
      else TD(coeff(v,pd[op(1,q)]),op(2,q))*pd(f,q)
      fi
    end, [op(vars(f) minus `b/var/s`)], v, f), `+`)
end:

# Point symmetries

papply := proc(v,f)
  convert(map(
    proc(q,v,f) 
      if type (q,`b/var`) then coeff(v,pd[q])*pd(f,q)
      elif type (q,`f/var`) then coeff(v,pd[q])*pd(f,q)
      else `papply/j`(op(q),v)*pd(f,q)
      fi
    end, [op(vars(f))], v, f), `+`)
end:

`papply/j` := proc(u,x,v)
  if `count/length`(x) = 1 then TD(coeff(v,pd[u]),x)
    - convert(map(`papply/j/1`, [op(`b/var/s`)], `count/f`(x), 1, u, v), `+`)
  else TD(`papply/j`(u,`count/r`(x),v),`count/f`(x))
    - convert(map(`papply/j/1`, [op(`b/var/s`)], `count/f`(x),`count/r`(x),
      u, v), `+`)
  fi
end:

`papply/j/1` := proc(y,x,z,u,v)
  TD(coeff(v,pd[y]),x)*jet(u,z*y)
end:

#
#   C o n v e r s i o n   t o   a n   o p e r a t o r
#

# a = expression, fl = list of undeterminates
# a must be linear in undeterminates or derivatives thereof

`convert/linop` := proc (a,fl)
  if type (a,'list') then
    linalg[stack](op(map(`convert/linop/1`,a,fl)))
  elif type (a,'algebraic') then `convert/linop/1`(a,fl)
  else ERROR(`the argument must be a list or an expression`) 
  fi
end:

`convert/linop/1` := proc (a,fl)
  local b,ts,ts1,t,i,f,aux,ans; 
  b := frontend(expand,[a]);
  ts := `convert/linop/1/1`(b,fl);
  ans := array(1..nops(fl));
  for i to nops(fl) do
    f := fl[i]; 
    aux := 0;
    ts1 := select(proc(t,f) type(t,'function') and op(1,t) = f end, ts, f);
    for t in ts1 do
      if type(b,linear(t)) then
        aux := aux + coeff(b,t,1)*op(0,t)[op(2,t)];
        b := coeff(b,t,0)
      else ERROR(`not linear in a derivative`, t)
      fi
    od;
    if member(f,ts) then
      if type(b,linear(f)) then
        aux := aux + coeff(b,f,1);
        b := coeff(b,f,0)
      else ERROR(`not linear in an undeterminate`, f, b)
      fi
    fi;
    ans[i] := aux
  od;
  if b = 0 then op(ans)
  else ERROR(`unable to convert to a linear operator`, b)
  fi;
end:

`convert/linop/1/1` := proc(a,fl)
  if type (a,specfunc(anything,TD)) and member(op(1,a),fl) then {a}
  elif type (a,specfunc(anything,pd)) and member(op(1,a),fl) then {a}
  elif type (a,'name') and member(a,fl) then {a}
  elif type (a,{`+`,`*`}) then `union`(op(map(procname,[op(a)],fl)))
  else {}
  fi
end:

#
#   T r a n s f o r m
#

transform := proc()
  local es,e,fs,x,q,xt,qt,i,j,A,B;
  es := select(type,[args],`=`);
  fs := select(type,[args],algebraic);
  if nops(es) + nops(fs) <> nargs then ERROR(`invalid arguments`) fi;
  if nops(es) = 0 then ERROR(`no transformation`) 
  else
    xt := table([seq(x=x, x=`b/var/list`)]);
    qt := table([seq(q=q, q=`f/var/list`)]);
    for e in es do 
      if type(op(1,e),`b/var`) then xt[op(1,e)] := op(2,e)
      elif type(op(1,e),`f/var`) then qt[op(1,e)] := op(2,e)
      else ERROR (`wrong variable on lhs`, op(1,e))
      fi
    od; 
    A := linalg[matrix](`b/dim`,`b/dim`,[]);
    for i from 1 to `b/dim` do
      for j from 1 to `b/dim` do 
        A[i,j] := TD(xt[`b/var/list`[i]],`b/var/list`[j])
      od
    od; 
    B := traperror(linalg[inverse](A));
    if B = lasterror then ERROR (`noninvertible transformation`) fi
  fi;
  if nops(fs) = 0 then RETURN() fi;
  if nops(fs) = 1 then `transform/1`(fs[1],xt,qt,B); 
  else op(map(`transform/1`,fs,xt,qt,B))
  fi
end:

`transform/1` := proc(f,xt,qt,B)
  if type(f,constant) then f
  elif type(f,`b/var`) then xt[f] 
  elif type(f,`f/var`) then qt[f] 
  elif type(f,`j/var`) then `transform/j`(op(f),xt,qt,B) 
  elif type(f,{`+`,`*`,`^`}) then map(procname,f,xt,qt,B)
  elif type(f, specfunc(anything,pd)) then `transform/pd`(op(f),xt,qt,B) 
  elif type(f, specfunc(anything,TD)) then procname(evalTD(f),xt,qt,B)
  elif type(f,'name') then f
  else map(procname,f,xt,qt,B)
  fi
end:

`transform/j` := proc(u,x,xt,qt,B)
  option remember;
  local x1,q,i,j;
  x1 := `count/f`(x);
  if x1 = x then q := `transform/1`(u,xt,qt,B) 
  else q := `transform/1`(jet(u,`count/r`(x)),xt,qt,B)
  fi;
  for j while x1 <> `b/var/list`[j] do od; 
  convert([seq(B[i,j]*TD(q,`b/var/list`[i]), i=1..`b/dim`)], `+`)
end:

`transform/pd` := proc(f,z,xt,qt,B)
  option remember;
  local z1,q,i,j;
  if not type (z,`b/count`) then ERROR(`cannot do pd`) fi;
  z1 := `count/f`(z);
  if z1 = z then q := f 
  else q := `transform/1`(pd(f,`count/r`(z)),xt,qt,B)
  fi; 
  for j while z1 <> `b/var/list`[j] do od; 
  convert([seq(B[i,j]*pd(q,`b/var/list`[i]), i=1..`b/dim`)], `+`)
end:

#
#   V a r i a t i o n s
#

variation := proc (f,p)
  if not type(p,`f/var`) then ERROR(`not a fibre variable`, p) fi;
  convert (map (proc (q,f,p)
    if q = p then pd(f,q)
    elif type (q, `j/var`) and op(1,q) = p then
      `count/sgn`(op(2,q)) * TD(pd(f,q), op(2,q))
    else 0
    fi
  end, [op(vars (f) minus `b/var/s`)], f, p), `+`)
end:

# Compute the Tonti lagrangian

lagrangian := proc ()
  local arge,argn,ht,et;
  ht := op(select(type,[args],'table'));
# argn := select(type,[args],'name');
  arge := select(type,[args],`=`);
# if argn = [] then argn := NULL
# else op(argn)
# fi;
  argn := NULL;
  et := table (arge);
  convert(map(
    proc (q,et,ht)
      local inttype,aux; global _htt;
      inttype := args[4..nargs];
      if not assigned (et[q]) then
        ERROR (`no EL expression for a field identifier`, q)
      fi;
      if not assigned (ht[q]) then
        ERROR (`no homotopy for a field identifier`, q)
      fi;
      aux := simpl(eval(subs(_htt = 1, ht[q])));
      if aux <> q then ERROR(`not a homotopy`, aux <> q) fi;
      aux := simpl(pd(eval(subs(_htt = 0, ht[q])), q));
      if aux <> 0 then ERROR(`not a homotopy`, aux, `not constant`) fi;
      int(`lagrangian/1`(et[q],ht)*pd(ht[q],_htt), _htt=0..1, inttype)
    end, [op(`f/var/s`)], et, ht, argn), `+`)
end:

`lagrangian/1` := proc (f,ht)
  global _htt;
  if type (f, 'constant') then f
  elif type (f, 'name') then
    if type (f, `f/var`) then ht[f]
    elif type (f, `b/var`) then f
    else f
    fi
  elif type (f, `j/var`) then TD(ht(op(1,f), t), op(2,f))
  elif type (f,{`+`,`*`,`^`}) then map (procname, f, ht)
  elif type (f,'function') then
    if type (f,specfunc(anything,'pd')) then
      map (procname, `pd//D`(f), ht)
    else map (procname, f, ht)
    fi
  else ERROR (`unexpected object`, f)
  fi
end:

`pd//D` := proc (f)
  local f1,x,fun,inds,i;
  f1 := op(1,f); x := op(2,f);
  if type (f1, specfunc(anything,'pd')) then f1 := procname (f1) fi;
  fun := op(0,f1); inds := op(f1);
  if [inds] = [x] then D(fun)(x)
  elif member(x,[inds],'i') then D[i](fun)(inds)
  else ERROR (`this should not happen`, f)
  fi
end:

parameter(_htt):

#
#  C o v e r i n g s
#

# Introducing additional fibre variables

newfibre := proc ()
  local flist;
  global `f/var/list`,`f/var/s`,`f/dim`,`f/<</list`,
    `b/var/list`,`n/var/list`;
  if nargs = 0 then
    ERROR(`arguments should be:\n
[list of additional fibre variables], optional maxorder`) 
  fi;
  flist := args[1];
  if not type(flist, list(name)) then
    ERROR(`fibre coordinates must be unassigned names`)
  fi;
  if nops([op(`b/var/list`),op(flist)])
     <> nops({op(`b/var/list`),op(flist)}) then
    ERROR(`coordinates must be mutually different`)
  fi;
  flist := select(proc(f) not type(f,`f/var`) end, flist);
  `f/var/list` := [op(`f/var/list`), op(flist)];
  `f/var/s` := {op(`f/var/list`)};
  `f/dim` := nops(`f/var/s`);
  `f/<</list` := `f/var/list`;
  `n/var/list` := [`n/var/list`, op(flist)]; 
  noderive(op(`n/var/list`));
  if nargs > 1 then `jet/aliases`(flist,args[2])
  else `n/var/list`
  fi
end:

`n/var/list` := []:

# Introducing additional equations 

covering := proc ()
  global `eqn/list`,`n/lhs/s`;
  local ns;
  if not type ([args], 'list'(`=`)) then 
    ERROR (`arguments not of type '='`)
  fi;
  `eqn/list` := select(proc(e,n) not member([op(1,e)], n) end,
    `eqn/list`,`n/lhs/s`);
  `eqn/list` := [op(`eqn/list`), op(map (proc (e);
    if not type (op(1,e), `j/var`) then 
      ERROR (`not a jet variable on lhs`, op(1,e))
    else (op(op(1,e))) = op(2,e)
    fi
  end, [args]))]; 
  ns := map(proc(a) [op(op(1,a))] end, {args});
  `n/lhs/s` := `n/lhs/s` union ns;
  map(proc(e) 'jet'(op(1,e)) = eval(op(2,e)) end, `eqn/list`);
  refresh (); 
  op(map(proc(e) 'jet'(op(1,e)) = op(2,e) end, `eqn/list`)) 
end:

`n/lhs/s` := {}:

# Test cross derivatives:

testcovering := proc ()
  global `eqn/list`;
  local q,es,i,j,ans;
  if not type ([args], 'list'(`f/var`)) then 
    ERROR (`arguments not fibre variables`)
  fi;
  ans := [];
  for q in [args] do
    es := select(proc(e,q) op(1,[op(1,e)]) = q end,
      `eqn/list`, q);
    for i from 1 to nops(es) do
      for j from i+1 to nops(es) do ans := [op(ans), 
        TD(op(2,es[i]),op(2,[op(1,es[j])]))
          - TD(op(2,es[j]),op(2,[op(1,es[i])]))]
      od
    od
  od;
  map(simpl,ans)
end:

# Introducing a BŠcklund transformation

BT := proc()
  global `BT/list`;
  if not type ([args],'list'(`=`)) then ERROR (`bad arguments`) fi;
  `BT/list` := [args]
end:

`BT/list` := []:

# Test whether BT is a BŠcklund transformation  

testBT := proc()
  global `eqn/list`,`n/var/list`,`BT/list`;
  local el;
  el := select(proc(e,n) not member([op(1,e)], n) end, `eqn/list`,`n/lhs/s`);
  op(map(
    proc(e,qs) 
      if member(op(1,[op(1,e)]),`n/var/list`) then NULL
      else simpl(`convert/TD/1`('jet'(op(1,e)) - op(2,e), qs))
      fi
    end,el,`BT/list`))
end:

# Compute second projection of a vector field

proj := proc(a,q)
  if type (q,'nonnegint') then `proj/n`(a,q)
  elif type (q,var) then `proj/var`(a,q)
  else ERROR(`cannot handle this case`)
  fi
end:

`proj/n` := proc(a,n)
  local aux,u;
  global `BT/list`;
  if type (a,'constant') then a
  elif type (a,{`+`,`*`,`^`}) then map(procname,a,n) 
  elif type (a,`vectorfield/pd`) then
    if n = 0 then aux := []
    else aux := expand((1 + convert(`b/var/s`,`+`))^n - 1);
      aux := map(proc(x) x/coeffs(x) end, [op(sort(aux, `b/var/list`))])
    fi;
    convert(map(
      proc(e,a,aux) local e1,e2;
        e1 := op(1,e); e2 := op(2,e);
        pd(e2,op(a))*pd[e1] + 
        convert(map(
          proc(x,a,e1,e2)
            if not nojet(e1,x) then
              pd(TD(e2,x),op(a))*pd['jet'(e1,x)]
            else NULL
            fi
          end, aux,a,e1,e2),`+`)
      end,`BT/list`,a,aux),`+`)
  elif type (a,`vectorfield/TD`) then
    ERROR (`TD's should have been already evaluated`)
  elif type (a,'name') then a
  elif type (a,'function') then a
  fi  
end:

nojet := proc(u,x)
  global `eqn/list`;
  local e,e1;
  for e in `eqn/list` do
    e1 := [op(1,e)];
    if u = op(1,e1) and (x = op(2,e1) or type (x/op(2,e1),'count')) then
      RETURN(true)
    fi
  od;
  false
end:

`proj/q` := proc(a,q)
  local aux,u;
  global `BT/list`;
  if type (a,'constant') then a
  elif type (a,{`+`,`*`,`^`}) then map(procname,a,n) 
  elif type (a,`vectorfield/pd`) then
    aux := expand((1 + convert(`b/var/s`,`+`))^n - 1);
    aux := map(proc(x) x/coeffs(x) end, [op(sort(aux, `b/var/list`))]);
    convert(map(
      proc(e,a,aux) local e1,e2;
        e1 := op(1,e); e2 := op(2,e);
        pd(e2,op(a))*pd[e1] + 
        convert(map(
          proc(x,a,e1,e2)
            if 'jet'(e1,x) = jet(e1,x) then
              pd(TD(e2,x),op(a))*pd['jet'(e1,x)]
            else NULL
            fi
          end, aux,a,e1,e2),`+`)
      end,`BT/list`,a,aux),`+`)
  elif type (a,`vectorfield/TD`) then
    ERROR (`TD's should have been already evaluated`)
  elif type (a,'name') then a
  elif type (a,'function') then a
  fi  
end:

TDfield := proc(z,n)
  local aux,u;  
  aux := expand((1 + convert(`b/var/s`,`+`))^n - 1);
  aux := map(proc(x) x/coeffs(x) end, [op(sort(aux, `b/var/list`))]);
  pd[z] + convert(map(
    proc(f,z,aux) 
      TD(f,z)*pd[f] + convert(map(
        proc(x,f,z)
          if 'jet'(f,x) = jet(f,x) then
            jet(f,x*z)*pd['jet'(f,x)]
          else NULL
          fi
        end, aux,f,z),`+`)
    end,`f/var/list`,z,aux),`+`)
end:

#
#  L i n e a r   c o v e r i n g s
#

# Making a ZCR from a linear covering

lincoveringmatrix := proc(x,ql,P)
  local el,m,n,i,j,a,r,ans,P0;
  if type (x,'list') then el := x
  else el := map(TD,ql,x)
  fi;  
  m := nops(el);
  n := nops(ql);
  if nargs > 2 then P0 := linalg[matrix](m, 1, 0) fi;
  ans := linalg[matrix](m, n, 0); 
  for i to m do
    a := el[i]; r := a;
    for j to n do
      if type(a, linear(ql[j])) then
        ans[i,j] := coeff(a,ql[j],1);
        r := r - ans[i,j]*ql[j]
      fi
    od;
    if nargs > 2 then P0[i,1] := simpl(r) fi
  od;
  if nargs > 2 then P := op(P0) fi;
  op(ans)
end:

# Making a Lie algebra from matrix generators

mla := proc()
  local M,m,n,P,Q,K,i,j,S,t,k,l;
  M := matrices2rows(args); m := rowdim(M); n := coldim(M);
  Q := array(identity, 1..n, 1..n);
  P := gaussjord(concat(transpose(M),Q), m);
  Q := submatrix(P, 1..n, (m + 1)..(m + n));
  P := submatrix(P, 1..n, 1..m);
  K := kernel(P);
  if K <> {} then
    print(op(K));
    ERROR(`the input matrices are not independent`)
  fi;
  t := table(antisymmetric,sparse,[]);
  for i to nargs do
    for j from i+1 to nargs do
      S := evalm(args[i]&*args[j] - args[j]&*args[i]);
      K := kernel(concat(P, evalm(Q&*transpose(matrix2row(S)))));
      if K <> {} then K := op(K);
        K := [seq(-K[l]/K[m+1]*args[l], l=1..m)];
        k := convert(K,`+`);
        if k <> 0 then t[args[i],args[j]] := k fi;
      else t[args[i],args[j]] := op(S)
      fi
    od
  od;
  op(t)
end:

matrix2row := proc(A)
  local i;
  concat(seq(stack(row(A,i)), i=1..rowdim(A)))
end:

matrices2rows := proc()
  local j;
  stack(seq(matrix2row(args[j]), j=1..nargs))
end:


# Computing the Killing form of a Lie algebra
# given by the table  t  and the list of generators  ls.

Kil := proc(t,ls)
  local b,n,i,j,k;
  n := nops(ls);
  b := matrix(n,n,[]);
  for i to n do
    for j to n do
      b[i,j] :=  0;
      for k to n do
        b[i,j] := b[i,j] 
          + coeff(`mla/ad`(ls[i], `mla/ad`(ls[j],ls[k],t,ls), t,ls), ls[k]);
      od
    od
  od;
  op(b)
end:

bra := proc(a,b,t,ls)
  local al,bl,ax,bx,ans;
  if type(a,`+`) then al := [op(a)] else al := [a] fi;
  if type(b,`+`) then bl := [op(b)] else bl := [b] fi;
  al := map(`bra/1`, al,ls); 
  bl := map(`bra/1`, bl,ls); 
  ans := 0;
  for ax in al do
    for bx in bl do
      ans := ans + op(1,ax)*op(1,bx)*t[op(2,ax),op(2,bx)]
    od
  od;
  ans
end:

`bra/1` := proc(q,ls)
  local q1,q2;
  if type(q,`*`) then q1 := op(1,q); q2 := op(2,q);
    if member(q1,ls) then q2 := op(1,q); q1 := op(2,q) fi;
    RETURN([q1,q2])
  else RETURN([1,q])
  fi 
 end:

ad := proc(a,t,ls)
  local i,j,n,ans,ai;
  n := nops(ls);
  ans := matrix(n,n,0);
  for i to n do
    ai := bra(a,ls[i],t,ls);
    for j to n do
      ans[i,j] := ans[i,j] + coeff(ai, ls[j]);
    od
  od;
  op(ans)
end:

#
#  L a x   p a i r  ---->  Z C R 
#

LA := proc(L,A,x,t,P)
  local i,j,r,X,T;
  if nargs < 2 then
    ERROR(`Usage: LA(L-list, A-list, x, t)`) fi;
  if not type([L,A],list(list)) then
    ERROR(`First two arguments must be lists`) fi;
  if not type([t,x],list(`b/var`)) then
    ERROR(`Third and fourth argument must be base variables`) fi;
  r := nops(L);
  X := matrix(r,r,proc(i,j) if j-i = 1 then 1 else 0 fi end);
  for j from 1 to r do X[r,j] := L[r-j+1] od;
  T := matrix(r,r,0);
  for j from 1 to r do T[1,j] := A[r-j+1] od; 
  for i from 2 to r do
    for j from 1 to r do T[i,j] := T[i,j] + TD(T[i-1,j],x) od; 
    for j from 2 to r do T[i,j] := T[i,j] + T[i-1,j-1] od; 
    for j from 1 to r do T[i,j] := T[i,j] + T[i-1,r]*X[r,j] od 
  od;
  if nargs > 4 then
    P := map(normal, evalm(TD(X,t) - TD(T,x) + X&*T - T&*X))
  fi;
  op(X), op(T)
end:

#
#  Z C R  ---->  c h a r a c t e r i s t i c   e l e m e n t
#

char := proc() # syntax: char(x = A, y = B)
  global `eqn/list`;
  local x,y,A,B,`_eqn/list`,`_unk/s`,ans;
  `_eqn/list` := `eqn/list`;
  if not type ([args],'list'(`=`)) then
    ERROR(`arguments must be x = A, y = B`)
  fi;
  x := op(1,args[1]); A := op(2,args[1]);
  y := op(1,args[2]); B := op(2,args[2]);
  ans := traperror(`char/1`(x,A,y,B,`_eqn/list`));
  `eqn/list` := `_eqn/list`;
  refresh();
  if ans = lasterror then ERROR (lasterror) fi;
  op(ans)
end:

`char/1` := proc(x,A,y,B,`_eqn/list`)
  global `eqn/list`;
  local `_char/1`,e,ex,C,CC,chlist,chsubs,tab,ts,t,ans;
  `eqn/list` := map(
    proc(e,ch)
      (op(1,e)) = simpl(eval(op(2,e))) + ch[op(1,e)]
    end, `_eqn/list`,`_char/1`);
  refresh();
  C := map(evalTD, evalm(TD(A,y) - TD(B,x) + A&*B - B&*A));
  ts := `union`(op(map(`char/1/ts`,
    map(proc(e) op(2,e) end, op(3,op(C)))))); # print(`ts =`, ts);
  chlist := map(proc(e,ch) ch[op(1,e)] end, `_eqn/list`,`_char/1`);
  for e in `_eqn/list` do
    ex := op(1,e);
    chsubs := map(
      proc(ch,ex) 
        if [op(1,ch)] = [ex] then NULL else ch = 0 fi
      end, chlist, ex);
    CC := map(eval, subs(chsubs, op(C)));
    CC := map(collect, CC, {op(chlist)} union 
      map(proc(t,ch) TD(ch,t) end, ts, `_char/1`[ex]), simpl);
    ans[ex] := map(eval, subs(`_char/1`[ex] = 1, op(CC)));
    for t in ts do
      tab[t] := map(coeff, CC, 'TD'(`_char/1`[ex],t), 1)
    od;
    if has(ans[ex],`_char/1`) then ERROR(`this should not happen`) fi;
    for t in ts do 
      ans[ex] := evalm(ans[ex] + `count/sgn`(t)*`char/1/TD`(tab[t],t,A,B,x,y))
    od;
    ans[ex] := map(simpl,ans[ex]);
  od;
  map(proc(e,ans) ans[op(1,e)] end, `_eqn/list`, op(ans)) 
end:

`char/1/ts` := proc(a)
  if type (a,{'constant','ar'}) then {}
  elif type (a,'name') then {}
  elif type (a,{`+`,`*`,`^`,`=`}) then
    `union`(op(map(procname, [op(a)])))
  elif type (a,'function') then 
    if type (a,specfunc(anything,pd)) then {}
    elif type (a,specfunc(anything,TD)) then
      if cat(op(0,op(1,a))) = `_char/1` then {op(2,a)} else {} fi
    else `union`(op(map(procname, [op(a)])))
    fi
  else ERROR (`unexpected object`, a) 
  fi
end:

`char/1/TD` := proc(C,t,A,B,x,y)
  local t1,tr,ans;
  tr := t;
  ans := C;
  while not evalb([tr] = []) do 
    t1 := `count/f`(tr);
    tr := `count/r`(tr);
    if cat(t1) = cat(x) then
      ans := evalm(TD(ans,x) - A&*ans + ans&*A)
    elif cat(t1) = cat(y) then
      ans := evalm(TD(ans,y) - B&*ans + ans&*B)
    else ERROR(`not a base variable`, t1)
    fi
  od;
  op(ans)
end:

# Print settings

lprint(cat(`Blimit = `,Blimit,
`  ressize = `,ressize,
`  putsize = `,putsize,
`  maxsize = `,maxsize)): 

# save `Jets.m`;



