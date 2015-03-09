# J e t s 
#
# Differential calculus on jet spaces and diffieties
#

#
# See http://jets.math.slu.cz/ for further details
#

#
# A u t h o r s
#
# (c) 1999-2004 by Michal Marvan
# (c) 2005-2010 by Hynek Baran and Michal Marvan
#
#
#  L i c e n s e
#
# JETS is a free software distributed under the terms of the GNU General 
# Public License <http://www.gnu.org/copyleft/gpl.html> as published by 
# the Free Software Foundation.
#
# In particular, JETS comes with ABSOLUTELY NO WARRANTY.
#
# 
# A c k n o w l e d g m e n t s
#
# The first-named author was supported by GACR under project 201/07/P224
#


#
# History of changes
#
# v. 5.7  rel. 8 Dec 2010
# * Based on Jets code v. 5.6 as of 20 Jan 2010
#
# v. 5.71 rel. 4 Jan 2011
# * `divideout/unks/1`(): approved, better handling of polynomials
#
# v 5.72
# * `index/traceless` matrix index function added
# * store(): formatting of output of assignments changed (each on separate line now)
# * new `jet/gen/all` and `count/gen/all` functions 
#
# v 5.73 alpha
# * first attempt to fix a critical bug in `cc/new` (some cc's was omitted by run)
#
# v 5.73 beta
# * `divideout/unks`, `type/divideout`: fixed (it was ok in very old jets but broken later)
#   and little improved ((exp(F)+1) is divided out now)
# * Varordering: new ordering revdeg implemented;
#   [degree, revdeg] is equivalent to the graded reverse lexicographic order (tdeg or grevlex)
# * `resolve/normalizer` added
# * Reporter implemented (quite primitive, resolve only)  
#
# v 5.74 alpha
# * resolve completly rewritten
# * started use of parallel MaP version of map (in resolve and derive) but no still not supported by Maple 16
# * derive redesigned
# * new functions Varl, VarL, LVar
# * minor evalTD bug fixed (wrong result on matrices) 
# * nonzero() bug (missing factor@) fixed (probably big issiue)
# * minor bug in Varordering fixed (if none fiber vars)
# * `resolve/nonresrat` limit introduced (price overlap of resolvable epr. over nonresolvable enforces FAIL of resolve)
# * minor improvements in reporting of assembled cc's
# * TestUnkOrd() introduced
# * sizefactor
# * `resolve/lin/price` back in the simplest form
# * `divideout/normalizer` added
# * Maple 14 compatibilty
#
#
# v 5.75 
# * old resolve is default
#
# v. 5.76
# * apply fixed (last ERROR replaced with unevaluated apply)
#
# v 5.77
# * `derive/1` : treating of polynoms and sums disabled (a bug found)
#
# v 5.78
# package JetMachine introduced
# JetMachine:-Consequences introduced
# * `jet/gen/all` fixed
# * `convert/crack` introduced
# * reenabled Vars to accept sequential arguments
# * uncomment the directive bellow to enable the new resolve implementation
#$define jets_new_resolve_enable 


###########################################################################################
###########################################################################################
# Initialization and configuration
###########################################################################################
###########################################################################################

interface(screenwidth=120):
print(`Jets 5.78 for Maple 15 as of Oct 26, 2012`);

#
# Source code configuration, options and parameters
#

### version info
`Jets/opts`["Version", "core"]  := [5,7,8]:
`Jets/opts`["Version", "CC"]    := ["MM_SSICOS", 2, 0] :
`Jets/opts`["Version", "Maple"] := table(["Tested"={15}, "Minimal"=14]):

### optional features
# Some parts of Jets source code is disbbled by default,
# since it is not proprely finished or tested yet.
# Use assignments bellow (before reading Jets.s in) to enable such additional code.

#`Jets/opts`["Optionals"]["Multiord"] := true:
#$define jets_new_resolve_enable 

#
# Debugging
#

### reporting
#
# Reporting about the progression of calculation is available independently of debug mode bellow.
# Syntax: reporting(derive = 0, resolve = 0, run = 0, cc = 0, pd = 0); 

### debug mode switch
#
# Some debugging functionality (as fuction arguments type checks, assumptions or logging) 
# is disabled by default but may be turned on by the macro bellow. 
# A lot of computing time is saved when debug mode is disabled, 
# but the AssertLevel() function and some more debugging functionality is not available.
# Turning debugging mode on may dramatically harm the time and memory usage.
#
# In the case of any problem (as an error raised or wrong result returned),
# please turn the debugging mode ON by removing the very first character # in the line bellow:
#
#$define jets_mode_debugging # <<<- TURN ON DEBUG MODE HERE by UNcommenting this line #  <- DEBUG ON/OFF


### debugging code
$ifdef jets_mode_debugging
# the case when debugging is ON:
print(`debugging mode enabled`);
print(kernelopts(version));
kernelopts(opaquemodules=false): 
$define ATC(a,t) a::t # Arguments Type Control enabled
$define DOE(a) a      # Debug Only Expressions enabled
$else
# the case when debugging is OFF:
$define ATC(a,t) a # Arguments Type Control disabled
$define DOE(a)     # Debug Only Expressions ignored
$endif

#
# Initialization tests
#

### single load test
# make sure that this source file is not already loaded:
if assigned(cat(`jets/read/flag/`,__FILE__)) then error "source file %1 already loaded.", __FILE__; fi;
if assigned(cat(`jets/read/flag/`,__FILE__)) then `quit`(255); fi; # force immediate exit from read() statement
assign(cat(`jets/read/flag/`,__FILE__), true):

### aux macros
$define Report(l, m) if rt > l then report(lb,[cat('procname','`:`'), op(m)]) fi;


##############################
#MaP := evalf(Threads[Map]);
MaP := evalf(map):

#
# old Maple version backward compatibility
#
# the routines defined in newer versions only are called as compat[routine]
# in the code bellow are these routines 
# - assigned to this auxiliary table (if available in the current version)
# - implemented by Hynek for backward compatibility 

### Maple 14 is probably the minimum
if not(assigned(DifferentialAlgebra)) then # DifferentialAlgebra available since Maple 14
  lprint(kernelopts(version));
  error "Maple older than 14 detected, Jets cannot be used.";
fi;
if not(assigned(DifferentialAlgebra)) then
  `quit`(255);
fi;
### Maple 15 features:
if not(assigned(numelems)) then # numelems available since Maple 15
  printf("Warning: Maple of version older than 15 detected. Please upgrade to Maple 15.\n%s\n", kernelopts(version));
  compat[Record[packed]]:= Record: # Record[packed] not available, use Record instead
else
  # we have Maple 15 (or newer)
  compat[Record[packed]] := Record[packed]:
fi:

###########################################################################################
###########################################################################################
# Jets - Main procedures
###########################################################################################
###########################################################################################

# This is a set of main routines based on the original Jets.s by MM

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

Existing := proc(c,a) assigned(c||a) end:
Call := proc(c,a) c||a end: # || replaces . since 6.0
    
# sorting by size

size := proc() # HB generalized size of any number of arguments
  #try 
    add(`size/1`(a), a in [args]);
  #catch:
  #  printf("\nsize: failed and returned infinity: %q\n", 
  #         StringTools[FormatMessage](lastexception[2..-1]));
  #  infinity;
  #end:
end:

sizefactor := 1000000000:
`size/1` := proc(a) # MM size evaluator
  global sizefactor;
  evalf(nops(Vars(a)) + length(a)/sizefactor)
end:


#sizesort := proc(ql,pr)  # ql = list of expressions, pr = sizeing proc
#  local qls;
#  qls := map(proc(q,pr) [q,pr(q)] end, ql, pr);
#  qls := sort(qls, proc(a,b) evalb(op(2,a) < op(2,b)) end);
#  map (proc(a) op(1,a) end, qls)
#end:
sizesort := proc(L::list, sizef)
local l;
    return map(attributes,sort([seq](setattribute(SFloat(sizef(l),0),l), l=L),`<`));
end proc:
# see http://www.mapleprimes.com/blog/joe-riel/sorting-with-attributes

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
# `transform/count`(x) :=  the product of non-negative powers in x # = numerator 
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

#`transform/count` := proc(x)
#  local aux;
#  if type (x,`^`) then if op(2,x) < 0 then 1 else x fi
#  elif type (x,`*`) then aux := map(`transform/count`, x);
#  else x
#  fi
#end:

`transform/count` := op(numer):

`count/gen/all` := proc(b::list, m::{posint,0}) # HB
  description "Generates all counts in variables b up to m-th order";
  `count/gen/all/1`(b,m)[2..-1]; # 1 is not a count
end:

`count/gen/all/1` := proc(b::list, m::{posint,0}) # HB
  if nops(b) = 0 or m<=0 then 
    1
  else
    seq(seq(i*j, j in [procname(b[2..-1], m-`count/length`(i))]), i in seq(b[1]^i, i=0..m));
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
  js := sort([op(map(varorder,`vars/1`(f)))]);
  op(nops(js),js)
end:

jetorders := proc(f) # HB
  op(map(varorder,`vars/1`(f)))
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
  #aux := expand((1 + convert(`b/var/s`,`+`))^r - 1);  
  #aux := map(proc(a) a/coeffs(a) end, [op(sort(aux, `b/var/list`))]);
  aux := sort([`count/gen/all`(`b/var/list`, r)]); # HB
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
  local f,fs,es,e, opts; 
  global `dep/tab`;
  fs := select(type, {args}, function);
  es := select(type, {args}, `=`);
  opts := select(type, {args}, symbol); # HB
  if fs union es union opts <> {args} then # HB
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
  # HB:
  if `subs` in opts then
    seq((op(1,e)=op(1,e)(op(op(2,e)))), e = es) 
  else  
  # :HB
    seq(op(1,e) = op(2,e), e = es)
  fi   
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
  if type (f,{'numeric', 'complex'}) then 0 # HB 5. 5. 2008
  elif type (f,'name') then
    if member (f,[constants]) then 0
    elif type (f,`b/var`) then if f = x then 1 else 0 fi
    elif type (f,`f/var`) then jet(f,x)
    elif type (f,'parameter') then 0
    elif type (f,'dep') then
      if `vars/1`(f) minus `b/var/s` = {} then pd(f,x)
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
        if `vars/1`(op(1,f)) minus `b/var/s` = {} then pd(op(1,f), x*op(2,f))
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
  if type(f,sequential) or type(f, matrix) then # HB
    map('procname', f, args[2..-1])
  else
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
  fi;
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
  if type (f,{'numeric', 'complex'}) then 0 # HB 5. 5. 2008
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
  qs := [op(`vars/1`(f))];
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
# HB:
# there is an example how to specify derivatives of general function:
`der/MyFun`    := proc (der,f,x) 'D_MyFun'(f)*der(f,x) end:
`der/D_MyFun`  := proc (der,f,x) 'D2_MyFun'(f)*der(f,x) end:
`der/D2_MyFun` := proc (der,f,x) 'D3_MyFun'(f)*der(f,x) end:
`der/D3_MyFun` := proc (der,f,x) 'D4_MyFun'(f)*der(f,x) end:
# :HB

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

`der/dilog` := proc (der,f,x) # AS
  (ln(f)/(1-f))*der(f,x)
end:

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

`pd/tab/print/unk` := proc(u) # print all assigments of unknown u stored in pd/tab
  global `pd/tab`;
  if assigned(`pd/tab`[u]) then
    map(i -> lprint('pd'(u,op(i))=pd(u,op(i))), [indices(`pd/tab`[u])])
  else
    printf("%a not found in pd/tab\n", u);
  fi
end:


#`pd/decomp` := proc(e)
#	 # decomposes pd(f,p) to (f,p) and f to (f,1)
#   if type (e,'name') then (e,1)
#   elif type (e,specfunc(anything,'pd')) then	(op(1,e), op(2,e))
#  else error e, "cannot be decomposed, its not symbol or pd" fi;
#end:




# put assigns values to pd's via `pd/tab` or `dep/tab`
put := proc()
  local e;
  if type ([args], 'list'(`=`)) then
    for e in args do 
    	#`put/items/add`(lhs(e));
    	`put/1`(op(e)) 
    od
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
    assign(p = a);
  elif type (p,specfunc(anything,'pd')) then
    if a = 0 and type (op(1,p),'dep') and type(op(2,p),'var') then 
      `dep/tab`[op(1,p)] := `dep/tab`[op(1,p)] minus {op(2,p)}
    else 
      `pd/tab`[op(1,p)][op(2,p)] := a
    fi;
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


#`put/items/add` := proc(e)
#  global `put/items/table`;
#  local f, p;
#  f, p := `pd/decomp`(e);
#  `put/items/table`[f] := `put/items/table`[f] union {p};
#end:
#
#`index/put/items/table` := proc(Idx::list,Tbl::table,Entry::list)
#    if (nargs = 2) then # get returns {} if unassigned
#        if assigned(Tbl[op(Idx)]) then Tbl[op(Idx)];
#        else {};
#        end if;
#    else # assign
#        Tbl[op(Idx)] := op(Entry);
#    end if;
#end proc:
#
#`clear/put/items` := proc()
#	 global `put/items/table`;
#	 `put/items/table` := table(`put/items/table`):
#end:
#
#`clear/put/items`():



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

# To convert the pd table into a list of expressions while clearing all
# assignments to pd's:

`clear/pds` := proc()
  local t,aux;
  global `pd/tab`;
  reduce();
  t := copy(`pd/tab`);
  `pd/tab` := table([]);
  refresh();
  #`clear/put/items`():
  aux := op(map(`pds/1`, op(2,op(t))));
  map(proc(e) op(1,e) - op(2,e) end, sizesort([aux], size)); # HB
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
            evalb(`vars/1`(p) minus `dep/tab`[f] = {}) 
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

`cc/time` := 0.0 :

# The old cc implementation
# This cc implementation is deprecated but still available, 
# if you need to use it globally, set 
# cc := proc() `cc/old`(args, _options) end:
# or you may call `cc/old`() at any moment without any side-effects

cc := proc() `cc/new`(args, _options) end:

`cc/old` := proc()
  local e,el,f,ft,zl,p,pl,q,i,j,p1,q1,z,ans,sl,aux,rt,lb,time0; 
  global `dep/tab`,`pd/tab`,`cc/s`,`cc/tab`,`cc/time`;
  time0 := time();
  ans := NULL; 
  zl := [];
  lb := `CC:`; rt := `report/tab`[cc];
  
  el := op(2,op(`dep/tab`)); # list of stored dependences
  if rt > 3 then report(lb,["looking for cc - dep/tab"]) fi;
  for e in el do 
    f := op(1,e); # an unknown
    ft := op(2,e); # its dependence set
    if rt > 3 then report(lb,[`dependence set:`, 'f' = f, 'ft'= ft]) fi;
    aux := NULL;
    if f <> eval(f) then # f assigned
      for p in `vars/1`(eval(f)) minus ft do
        # pd(f,p) should be zero
        aux := aux, [f, eval(f), p, 0, 1, 1] 
      od;
      zl := [op(zl), aux];
      if rt > 2 then report(lb,[f, cat(`ass/dep: `,nops(zl),` c.c.`)]) fi
    fi
  od;  
  
  if rt > 2 then report(lb,["looking for cc - pd/tab"]) fi;
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
          if `vars/1`(p) minus `dep/tab`[f] <> {} then
              # pd(f,p) should be zero 
            if ft[p] <> 0 then
              aux := aux, [f, ft[p], 1, 0, 1, `count/length`(p)]
            fi
          fi; 
          if ft[p] <> 0 then
            for q in `vars/1`(ft[p]) minus `dep/tab`[f] do
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
            if p*q1 <> q*p1 then ERROR(`this should not happen`) fi; # NejSpolNas
            aux := aux, [f, ft[p], q1, ft[q], p1, `count/length`(p*q1)] # ii kind
          fi
        od
      od;
      if rt > 2 then report(lb,[f, cat(`cross-derivatives: `,nops([aux]))]) fi;
      zl := [op(zl), aux];
    fi
  od;  
  
  if rt > 1 then report(lb,[cat(`total number: `,nops(zl),` c.c.`)]) fi;
  zl := [op({op(zl)} minus `cc/s`)];
  inc(`cc/count/total`, nops(zl));
  if rt > 1 then report(lb,[cat(`of them new: `,nops(zl),` c.c.`)]) fi;
  zl := select(proc(z,m) evalb(op(6,z) = m) end,
    zl, min(op(map(proc(z) op(6,z) end, zl)))); ## !
#   zl := select(
#     proc(z,zl) local z1;
#       for z1 in zl do
#         if type (op(6,z1)/op(6,z),'count') then RETURN(true) fi
#       od;
#       false
#     end, zl, zl);
   inc(`cc/count/computed`, nops(zl));
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
  inc(`cc/time`, time()-time0);
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

# The common initialization

`clear/cc` := proc()
  global `cc/s`,`cc/tab`;
  local T;
  `cc/s` := {};
  `cc/tab` := table([]);  
  if type(CC, `module`) then  ### new !
    CC:-init():
  fi;
  NULL
end:

### New cc iplementation

  CCSidePrice1:= proc(U, p, m)::numeric;
   option remember;
   local q, v, s;
   if `JetMonomTools/J`:-divide1(p,m,q) then
     s, v := `CCSidePrice1/1`(U,p); 
     if nops(`vars/1`(J2j(q)) minus v) > 0 then # trik: pd(U,p) does not depend on q=p/m
       return 0
     else
       return degree(q)*nops(v)*s; 
     fi
   else 
     error "Cannot compute price at %1: %2 |/ %3 ", U, p, m; 
   fi; 
  end:
  
  `CCSidePrice1/1` := proc(U,p)
    option remember;
    local P;
    P := pd(U,J2j(p));
    return (size(P)), `vars/1`(P);
  end:


#`cc/new` := proc({leaveTrivial::truefalse:=evalb(resultType=list), 
#            resultType::identical(set,list):=set, 
#            pop::truefalse:=false,
#            totalNumber::symbol:='None', # output parameter: 
#                              # total number of cc remaining (including the portion returned)
#            ##  keywords for selection of a "portion" of cc's
#            # In all parameters below, -1 means no limitation.
#            # At least 1 cc (if exists) is ALWAYS returned regardless of any selecting criteria.
#            # See CC:-cc for details.
#            maxnum::{posint,identical(-1)} := -1, # total maximum number of returned cc's
#            maxnumP::{posint,identical(-1)} := -1, # return the first maxnumP items and add all cc's of equal prices
#            maxprice::{numeric,infinity} := infinity # maximal price of cc's to be returned
#           }, $)
#  local T, ans, time0, cs, as, i; 
#  global rt, lb, `cc/count/total`, `cc/count/computed`, `cc/time`, cctab;
#  lb := `CC:`; rt := `report/tab`[cc];
#  time0 := time();
#  
#  T := j2J(`cc/pd/listall`()); 
#  
#  forget(CCSidePrice1);
#  cs := CC:-cc(T,  sidePriceFunction=CCSidePrice1,
#	             ':-pop'=pop, 
#	             ':-totalNumber'=totalNumber, # TODO(eff): viz nize
#							 ':-maxnum'=maxnum, ':-maxnumP'=maxnumP, ':-maxprice'=maxprice); 
#  as := map(`cc/ass`, J2j(cs));
#  rprintf(1, ["cc found %a are assembled as %a", cs, as]);
#  as := map(Simpl@eval, as) ; # map(simplify, as, size); ### ???
#  rprintf(1, ["cc found are %a", as]);
#  inc(`cc/count/total`, nops(cs));
#  if leaveTrivial then  
#    ans := as;
#    if rt > 0 then report(lb,[`number of c.c.:`, nops(ans)]) fi;
#  else 
#	  # remove 1=1 unless prohibited by leaveTrivial
#    ans := remove(`=`, as, 0); 
#    if nops(ans)=0 and eval(totalNumber) > nops(cs) then 
#			# at least 1 cc must be returned
#			i := 1;
#			while nops(ans)=0 and eval(totalNumber) > nops(cs) do
#        cs := CC:-cc(T,  sidePriceFunction=CCSidePrice1,
#				             ':-pop'=pop, 
#				             ':-totalNumber'=totalNumber, 
#				             ':-maxnum'=i);		
#				  # TODO(eff): Pravdepodobne bude rychlejsi namisto opakovaneho volani CC:-cc(':-pop'=pop)		
#				  # zavolat jen jednou cc(':-pop'=false), 
#				  # vybrat z vysledku co je potreba  a nakonec zavolat CC:-markFF na zvoleny vyber            
#			  as := map(`cc/ass`, J2j(cs));
#		    as := map(Simpl@eval, as) ; # map(simplify, as, size); ### ???
#			  rprintf(1, ["additional cc found %a and assembled as %a", cs, as]);
#        inc(`cc/count/total`, nops(cs));
#				ans := remove(`=`, as, 0);				
#				if not(pop) then i := i+1 fi;				
#			od;
#			if nops(ans)>0 then
#        if rt > 0 then report(lb,[`nontrivial cc (regardless of selecting criteria given) found`]) fi; 
#      else
#	      if rt > 0 then report(lb,[`None nontrivial cc (regardless of selecting criteria given) found`]) fi; 		  
#      fi;				
#	  else
#      if rt > 0 then report(lb,[`numbers of c.c.: nontrivial`, nops(ans), `trivial`, nops(as)-nops(ans)]) fi;   
#		fi;		
#  fi; 
#  forget(CCSidePrice1);
#  
#  inc(`cc/count/computed`, nops(ans));
#  inc(`cc/time`, time()-time0);
#  rprintf(1, ["There are %a cc at the moment. We have had computed %a of totally %a.", 
#              nops(ans),  `cc/count/computed`, `cc/count/total`]);
#  rprintf(3, ["cc are %q", ans]);
#  
#  if rt > 0 then report(lb,[`total c.c. number: `, `cc/count/total`, 
#                            `computed:`, `cc/count/computed`, `time:`, `cc/time`]) 
#  fi;
#  
#  map(eval, convert(ans,resultType));
#end:


`cc/new` := proc({leaveTrivial::truefalse:=evalb(resultType=list), 
            resultType::identical(set,list):=set, 
            pop::truefalse:=false,
            totalNumber::symbol:='None', # output parameter: 
                              # total number of cc remaining (including the portion returned)
            ##  keywords for selection of a "portion" of cc's
            # In all parameters below, -1 means no limitation.
            # At least 1 cc (if exists) is ALWAYS returned regardless of any selecting criteria.
            # See CC:-cc for details.
            maxnum::{posint,identical(-1)} := -1, # total maximum number of returned cc's
            maxnumP::{posint,identical(-1)} := -1, # return the first maxnumP items and add all cc's of equal prices
            maxprice::{numeric,infinity} := infinity # maximal price of cc's to be returned
           }, $)
  local T, ans, time0, cs, as, i; 
  global rt, lb, `cc/count/total`, `cc/count/computed`, `cc/time`, cctab;
  lb := `CC:`; rt := `report/tab`[cc];
  time0 := time();
  
  
  if rt > 1 then
    report(lb, "Dependences and `pd/tab` indices:");
    map(a->lprint('a'(op(vars(a)))=indices(`pd/tab`[a], nolist)), [indices(`pd/tab`, nolist)]);
  fi;
  
  T := j2J(`cc/pd/listall`()); 
  
  if rt > 2 then
    report(lb, "Looking for cc for :");
    map(t->lprint(op(t)=J2j(T[op(t)])), [indices(T)]);
  fi;
 
  
  forget(CCSidePrice1);
  if pop<>false then error "Unsupported pop option value %1", pop; fi;
  cs := CC:-cc(T 
               #,  sidePriceFunction=CCSidePrice1,
	             #':-totalNumber'=totalNumber, # TODO(eff): viz nize
							 #':-maxnum'=maxnum, ':-maxnumP'=maxnumP, ':-maxprice'=maxprice
							 ); 
  as := map(`cc/ass`, J2j(cs));
  rprintf(1, ["cc found %a are assembled as %a", cs, as]);
  as := map(Simpl@eval, as) ; # map(simplify, as, size); ### ???
  `cc/FF`(cs,as);
  rprintf(1, ["cc found are %a", as]);
  inc(`cc/count/total`, nops(cs));
  if leaveTrivial then  
    ans := as;
    if rt > 0 then report(lb,[`number of c.c.:`, nops(ans)]) fi;
  else 
	  # remove 1=1 unless prohibited by leaveTrivial
    ans := remove(`=`, as, 0); 
    if nops(ans)=0 and eval(totalNumber) > nops(cs) then 
			# if all cc returned immediately, co bellow is no needed 
			# # at least 1 cc must be returned
			# i := 1;
			# while nops(ans)=0 and eval(totalNumber) > nops(cs) do
      #   cs := CC:-cc(T, sidePriceFunction=CCSidePrice1,
			#                ':-totalNumber'=totalNumber, 
			#                ':-maxnum'=maxnum+i);		
			#     # TODO(eff): Pravdepodobne bude rychlejsi namisto opakovaneho volani CC:-cc(':-pop'=pop)		
			#     # zavolat jen jednou cc(':-pop'=false), 
			#     # vybrat z vysledku co je potreba  a nakonec zavolat CC:-markFF na zvoleny vyber            
			#   as := map(`cc/ass`, J2j(cs));
		  #   as := map(Simpl@eval, as) ; # map(simplify, as, size); ### ???
		  #   `cc/FF`(cs,as);
			#   rprintf(1, ["additional cc found %a and assembled as %a", cs, as]);
      #   inc(`cc/count/total`, nops(cs));
			#   ans := remove(`=`, as, 0);				
			#   if not(pop) then i := i+1 fi;				
			# od;
			if nops(ans)>0 then
        if rt > 0 then report(lb,[`nontrivial cc (regardless of selecting criteria given) found`]) fi; 
      else
	      if rt > 0 then report(lb,[`None nontrivial cc (regardless of selecting criteria given) found`]) fi; 		  
      fi;				
	  else
      if rt > 0 then report(lb,[`numbers of c.c.: nontrivial`, nops(ans), `trivial`, nops(as)-nops(ans)]) fi;   
		fi;		
  fi; 
  forget(CCSidePrice1);
  
  inc(`cc/count/computed`, nops(ans));
  inc(`cc/time`, time()-time0);
  rprintf(1, ["There are %a cc at the moment. We have had computed %a of totally %a.", 
              nops(ans),  `cc/count/computed`, `cc/count/total`]);
  rprintf(3, ["cc are %q", ans]);
  
  if rt > 0 then report(lb,[`total c.c. number: `, `cc/count/total`, 
                            `computed:`, `cc/count/computed`, `time:`, `cc/time`]) 
  fi;
  
  map(eval, convert(ans,resultType));
end:


`cc/FF` := proc(cs, as)
  zip(`cc/FF/1`, cs, as)
end:

`cc/FF/1` :=proc(c,a)
  if a=0 then 
    CC:-markFF(c[2],lhs(c[3]),rhs(c[3]),CC:-getHS()[c[1]]);
    return NULL;
  else
    return c
  fi;
end:
    

`cc/pd/listall` := proc()
  global `dep/tab`, `pd/tab`;
  local T, e, el, f, ft, ds;
  T := table();
  
  el := op(2,op(`dep/tab`)); # list of stored dependences
  for e in el do 
    f := op(1,e); # an unknown
    ft := op(2,e); # its dependence set
    T[f] := `vars/1`(eval(f)) minus ft;
		if f <> eval(f) then T[f] := T[f] union {1} fi; # f assigned
  od;
  #print('T'=eval(T)); 
  
  el := op(2,op(`pd/tab`)); # list of stored partial derivatives
  for e in el do
    f := op(1,e); # an unknown
    ft := op(2,e); # table of its derivatives
    ds := {op(map(lhs, op(2,op(ft))))};
		#print(DS1, f, ft, ds);
		if type(f,'dep') then
		 ds := map(proc(p) p, 
								       op(`vars/1`(p) minus `dep/tab`[f]),
								       op(`vars/1`(ft[p]) minus `dep/tab`[f])
							 end, ds);
		 #print(DS2, f, ft, ds);
		fi;
    if f <> eval(f) then ds := ds union {1} fi; # f assigned
    if assigned(T[f]) then T[f] := T[f] union ds else  T[f] := ds fi;
  od;
   
  return(eval(T));
end:


`cc/ass` := proc(c::uneval)
  global rt, lb;
  local u, r, p, q;
  lb := `CC:`; rt := `report/tab`[cc];
  u := c[1];
  r := c[2];
  p := lhs(c[3]);
  q := rhs(c[3]);
  #printf("cc of %a at %a:\n", u, r);
  #printf("%q\n", [''pd1''( 'PdNE'(u,p), r/p)            =  ''pd1''( 'PdNE'(u,q), r/q)]);
  #printf("%q\n", [''pd1''( `pd/noeval`(u,p), r/p)       =  ''pd1''( `pd/noeval`(u,q), r/q)]);
  #printf("%q\n", [pd1( `pd/noeval`(u,p), r/p)           =  pd1( `pd/noeval`(u,q), r/q)]);
  #printf("%q\n", [`pd/noeval`( `pd/noeval`(u,p), r/p)   =  `pd/noeval`( `pd/noeval`(u,q), r/q)]);

  #pd1( pd1(u,p), r/p) -  pd1( pd1(u,q), r/q);
  #lprint (u,r, p,q);
  if rt > 2 then 
    report(lb, "assembling cc of variable %a(%a) at %a in %a, %a:\n
               pd(%a, %a) = pd( pd(%a, %a), %a) === pd( pd(%a, %a), %a) = pd(%a, %a)", 
                u, vars(u), r, p, q, #[indices(`pd/tab`[u], nolist)],
                [vars(`pd/noeval`(u,p)), Vars(`pd/noeval`(u,p))], r/p, 
                u, p, r/p, 
                u, q, r/q,
                [vars(`pd/noeval`(u,q)), Vars(`pd/noeval`(u,q))], r/q)     
  elif rt > 1 then 
    report(lb, "assembling cc of variable %a(%a) at %a in %a, %a:\n
               pd( pd(%a, %a), %a) = pd( pd(%a, %a), %a)", 
                u, vars(u), r, p, q,
                u, p, r/p, 
                u, q, r/q);
   lprint("c = ",c);                
  fi;
  #rprintf(3, ["assembling cc pd( pd(%a, %a), %a) = pd( pd(%a, %a), %a)", u,p, r/p, u,q, r/q]);
  pd1( `pd/noeval`(u,p), r/p) -  pd1( `pd/noeval`(u,q), r/q);  			
end:

    
    

`pd/noeval` := proc(F,U)
  global `pd/tab`;
  local res;
  if U=1 then
    return eval(F)
  else
    res := eval(`pd/tab`[evaln(F)][U], 1); 
    if type(res, indexed) then # not found in `pd/tab`
			pd(F,U);
    else
     res
    fi;
  fi
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
  local V;
  global `Simpl/nocollect/s`;
  if  hasfun(f, TD) then 
    WARNING("Simpl has TD!!!"); 
    simpl(f);
  else
    if nargs > 2 then
      error "Too much arguments"
    elif nargs = 2 then
      V := args[2];
      assert(type(V,sequential));
    else
      V := Vars(f) ;
      V := select(proc(v,f) type(f,polynom(anything,v)) end, V, f);
      V := convert(V,set) minus `Simpl/nocollect/s`;
    fi;
    collect(f, V, distributed, simpl)
  fi;
end:

`Simpl/nocollect/s` := {}:

#
#   F i n d i n g   d e p e n d e n c e   s e t 
#

vars := proc({noWarn::truefalse:=false})
  `union`(op(map(`vars/1`, [_rest], _options))); # HB multiple arguments
end:

`vars/1` := proc(f, {noWarn::truefalse:=false})
# option remember;
  if type (f,'constant') then {}
  elif type (f,'name') then 
    if type (f,{`b/var`,`f/var`}) then {f}
    elif type (f,'parameter') then {}
    elif type (f,'dep') then select (type,`dep/tab`[f],'var')   
    else if not noWarn then WARNING ("unknown dependence %1 in vars.", f) fi; 
         {f}
    fi
  elif type (f,{`+`,`*`,`^`,sequential}) then `union`(op(map(procname,[op(f)], _options))) # HB
  elif type (f,'function') then 
    if type (f, specfunc(anything,jet)) then {f}
    elif type (f, specfunc(anything,pd)) then procname(op(1,f), _options)
    elif type (f, specfunc(anything,TD)) then `vars/TD` (op(f))
    else `union`(op(map(procname,[op(f)], _options)))
    fi
  else error("unexpected object %1 in vars.", f);
  fi
end:


`vars/TD` := proc (f,x) 
  option remember;
  if type (x,'name') then
    `vars/1`(f) union `union`(op(map(`vars/TD/1`,`vars/1`(f),x)))
  else `vars/TD`(f,`count/r`(x)) union
    `union`(op(map(`vars/TD/1`,`vars/TD`(f,`count/r`(x)), `count/f`(x))))
  fi
end:

`vars/TD/1` := proc (q,x) 
  option remember;
  `vars/1`(evalTD(TD(q,x))) 
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


`jet/gen/all` := proc() # HB
 description "Generates all internal jets of f up to n-th order";
 global `f/var/list`, `b/var/list`, `eqn/list`;   
 local f, n, cs, es;
 if nargs=1 and type(args[1], {posint,0}) then
   op(map(procname, `f/var/list`, args[1]));
 elif nargs=2 and type(args[1],`f/var`) and type(args[2], {posint,0}) then
   f := args[1];
   n := args[2];
   es := map(e -> [lhs(e)],`eqn/list`);
   es := select(e -> e[1]=f, es);
   es := map(e -> e[2], es); # counts of all assigned jets of f
   cs := [`count/gen/all`(`b/var/list`, n)]; # all counts up ti n-th order
   cs := remove(c-> ormap(e -> divide(c,e), es, c) , cs); # remove assigned jets
   f, op(sort(map2(jet,f,cs), `vars/<<`));
 else
   error "Wrong argument(s) %1", args;
 fi;
end:


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
    end, [op(`vars/1` (rhs) minus `b/var/s`)], rhs, Q), `+`)
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
    end, [op(`vars/1` (f) minus `b/var/s`)], f, Q), `+`)
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
    end, [op(`vars/1`(g) minus `b/var/s`)], fl, g), `+`)
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
    for q in (`vars/1` (rhs) minus `b/var/s`) do
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
    for q in (`vars/1` (rhs) minus `b/var/s`) do
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
    end, [op(`vars/1` (rhs) minus `b/var/s`)], rhs, Q), `+`))
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
  `convert/diff/1`(diff, f,es);
end:

`convert/crack` := proc(f)
  local es, Vs;
  es := {args[2..nargs]};
  Vs := map(proc(v) if type(v, specfunc(anything,pd)) then op(1,v) else v fi end, Vars(f));
  printf("load package ""crack"";\n");
  map(`convert/crack/f`, Vs, es);
  printf("CRACK (%q);\n", 
      {`convert/diff/1`(crack, f,es)}, 
      {}, 
      Vs, 
      {});
end:

`convert/diff/f` := proc(g, es) 
  local qs := ars(g); 
  if qs<> {} then g(op(eval(subs(es,qs)))) else g fi; 
end:

`convert/crack/f` := proc(g, es) 
  local qs := ars(g); 
  if qs<> {} then printf("DEPEND %q;\n", g, op(eval(subs(es,qs)))) fi; 
end:

`convert/diff/1` := proc(t, f, es) # common for diff & crack (distinguished by t)
  local f1, qs;
  if type (f,'constant') then f
  elif type (f,'name') then
    if type (f,`ar`) then eval(subs(es,f)) # HB
    else 
      if t=diff then `convert/diff/f`(f, es) else f fi
    fi
  elif type (f,{`+`,`*`,`^`}) then map2 (procname, t, f, es) # HB
  elif type (f,{sequential,array}) then op(map2 (procname, t, convert(f, list), es)) # HB
  elif type (f,'function') then  
    if type (f,`j/var`) then eval(subs(es,f))
    elif type (f, specfunc(anything,pd)) then f1 := op(1,f); qs := ars(f1); 
      if t=diff then
        'diff'(f1(op(eval(subs(es,qs)))),`count//seq`(eval(subs(es,op(2,f))))) # HB
      elif t=crack then
        'df'(f1,`count//seq`(eval(subs(es,op(2,f))))) # HB
      else 
        error "Wrong conversion type %1", t;
      fi;        
    elif type (f, specfunc(anything,TD)) then 
      ERROR(`unevaluated total derivative`)
    else map2 (procname, t, f, es)
    fi
  else ERROR (`unexpected object`, f)
  fi
end:

# HB:
# converting diff to pd

`convert/pd` := proc (f)
  if op(0,f)= 'diff' then `convert/pd/diff`(f)
  elif type (f, atomic) then f
  else map('procname', op(0,f)(op([seq(op(i,f),i=1..nops(f))])))
  fi
end:

`convert/pd/diff` := proc(f)
  if op(0,op(1, f))= 'diff' then
    pd(`convert/pd/diff`(op(1, f)), op(2,f))
  else
    pd(op(0,op(1, f)), op(2,f));
  fi
end:
# :HB

# Declaring unknowns

unks := proc(a)
  if type (a,{'constant','ar'}) then {}
  elif type (a,'name') then {a}
  elif type (a,{`+`,`*`,`^`,'sequential'}) then `union`(op(map(unks,[op(a)])))
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
    unks(f) union `union`(op(map(`unks/TD/1`,`vars/1`(f),x)))
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
    pars(f) union `union`(op(map(`pars/TD/1`,`vars/1`(f),x)))
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
  global `cc/count/total`, `cc/count/computed`, `derive/time`, `cc/time`;
  `cc/count/total`, `cc/count/computed` := 0,0;
   `derive/time`, `cc/time` := 0.0, 0.0;
  if nargs = 0 then
    error "Missing arguments"
  else
   `run/l`(op(map(`run/1`,[args])))
  fi;
end:

`run/1` := proc(a)  # applies run/l to entries of lists, sets, and matrices
  if type (a,sequential) then op(map(`run/1`,a))
  elif type (a,'matrix') then
    if type (a,'name') then
      op(map(proc(x) op(2,x) end, op(3,op(a))))
    else
      op(map(proc(x) op(2,x) end, op(3,a)))
    fi
  else a
  fi
end:


`rep/res` := proc() end:
`rep/cc` := proc() end:
`rep/der` := proc() end:

`run/getstep` := proc() global `run/currentstep`; `run/currentstep` end:

`run/currentstep` := 0:

`run/l` := proc()
  local as,eqs,aux,i,imax,ders, res,t,rt,lb,ncc, aux1;
  global `run/time`,`run/bytes`, putsize, ressize, runtransformations,
         RESOLVE, `run/currentstep`;
  if `unk/<</list` = [] then
    ERROR (`please set unknowns(name1, name2, ...)`) 
  fi;
  clear(cc,derive);
  `run/time` := time();
  `run/bytes` := kernelopts(bytesalloc);
  lb := `RUN:`; rt := `report/tab`[run];
  do i := 0;
    `run/currentstep` := `run/currentstep` + 1;
    if rt > 0 then report(lb, `Guessing correctness of unknowns ordering...`); TestUnkOrd() fi;
    if rt > 0 then report(lb,`Compatibility conditions ...`) fi;
    
    ### cc
    #print(KOKO,CC:-HS[g11]);
    #as := cc(pop,maxnumP=1); 
    as := cc();
    #as = the lowest compatibility conditions
    #MM#   as := map(derive, as); # derive differential consequences of cc
    #   if rt > 1 then
    #     report(lb,[`d.c.c.: `, op(sort(map(size,[op(as)])))])
    #   fi; #MM#
    if nops(as) > 0 then 
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
    if nops(as) = 0 then
      if rt > 1 then report(lb,[`no cc to be resolved`]) fi;
	  else
      #print(BOBO,CC:-HS[g11]);
      #print(LOLO);
      #map(print,as);
      #`pd/tab/print/unk`(g11);

      #print(LOLO);
      
      if rt > 1 then report(lb,[`cc sizes to be resolved(`, nops(as),`): `, op(sort(map(size,[op(as)])))]) fi;
      if rt > 2 then report(lb,[`cc [LVar=size] to be resolved:`, map(a->[LVar(a)=size(a)], as)]) fi;       
      if rt > 5 then report(lb,[`cc to be resolved:`, as]) fi;       
    fi;
    MultiOrdCC:-Write(op(as)); # send intermediate cc's to the world   

    
    ### dc
    if rt > 4 then report(lb,[`args to be derived:`, args]) fi;           
    if rt > 3 then report(lb,[`args to be derived [size,LVar]:`, map(a->[LVar(a)=size(a)], [args])]) fi;       
    
    ders := {derive(args)};
    ders := map(simpl,ders); # TODO(eff): je to simpl nutne?
    ders := select(proc(a) evalb(a <> 0) end, ders); 
    if rt > 1 then report(lb,[`derived: `, op(sort(map(size,[op(ders)])))]) fi;
    if runtransformations <> {} then
      for t in runtransformations do
        ders := ders union map(Simpl@t,ders)
      od;
      ders := select(proc(a) evalb(a <> 0) end, ders); 
      if rt > 1 then
        report(lb,[`transformed derived: `, op(sort(map(size,[op(ders)])))]);
        if rt > 3 then report(lb,[`transformed c.c.: `], op(as)) fi;
      fi
    fi;
    if rt > 5 then report(lb,[`all derived: `], op(ders)) fi;

    ### are we done?
    if nops(as)+nops(ders)=0 then 
      tprint(`Success!`);
		  if nops(cc()) > 0 then error "Implementation error: There are remaining cc's" fi;
		  RESOLVE := {};
      RETURN(op(as)) # TODO: co vratime???
		fi;       

    ## take cc's from the outside
    #aux1 := MultiOrdCC:-Pop(); 
    ##aux := map(simpl, aux1); ### ???
    #aux := aux1; ### ???
    #aux := remove(`=`, aux, 0);
    #if nops(aux1)>0 then
    #  if rt > 5 then report(lb,[`imported cc: `], aux1) 
    #  elif rt > 3 then report(lb,[`imported cc sizes: `], map(size, aux1)) 
    #  elif rt > 0 then report(lb,[`imported cc #: `, nops(aux1), `of them nontrivial #:`, nops(aux)] ) fi;
    #fi;
    ncc := nops(as);
    #as := as union aux;

		### resolve ALL compatibility conditions cc and some of differential consequences (dc)		
		if nops(ders)=0 then
      if rt > 1 then report(lb,[`no dc to be resolved`]) fi;
		  res := resolve(op(as)); # TODO(eff): nestaci `resolve/1`?
		else
      aux := `size/*/<`(ders, ressize);
      if nops(aux)=0 then WARNING("ressize too low"); aux := {sizemin(ders, size)} fi; # TODO(eff): 
                                                                    # udelej nove rychle `size/*/<`
      if rt > 1 then report(lb,[`dc sizes to be resolved(`, nops(aux),`): `, op(sort(map(size,[op(aux)])))]) fi;
      if rt > 2 then report(lb,[`dc [LVar=size] to be resolved:`, map(a->[LVar(a)=size(a)], aux)]) fi;       
      if rt > 5 then report(lb,[`dc to be resolved: `, op(aux), `selected of totally`, nops(ders)]) fi;
      res := resolve(op(as),op(aux)); # TODO(eff): nestaci `resolve/1`?
    fi;  
      
    if res = FAIL then
      if ncc=0 and rt > 1 then WARNING("Cannot resolve differential consequence(s) only, no cc present."); fi;
      RETURN (FAIL);
    else 
      if rt > 1 then report(lb,[`cc+dc sizes resolved:`, op(sort(map(size,[res])))]) fi;
      if rt > 2 then report(lb,[`cc+dc [LVar=size] resolved:`, op(map(a->[lhs(a)=size(a)], [res]))]) fi;    
      if rt > 3 then report(lb,[`cc+dc LVar=[size,VarL] resolved:`, op(map(a->lhs(a)=[size(a),VarL(rhs(a))], [res]))]) fi;                            
      if rt > 5 then report(lb,[`cc+dc resolved:`, res]) fi;
 
      # put the resolved results
      # lprint("BEFORE PUT");
      # `pd/tab/print/unk`(g11);
      `run/put`(res);
      #if as<>{} and map(simpl,as)<>{0} then print(CHYBA,as) fi;
      # lprint("AFTER  PUT");
      # `pd/tab/print/unk`(g11);
       
      if Bytes() > Blimit then reduce() fi
    fi
  od;        
end:

`size/*/<` := proc(as,upb) # TODO(eff): udelej nove rychle `size/*/<` s pouzitim sizesort
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
end:

`size/=` := proc(a,upb) evalb(size(a) = upb) end:
    
runtransformations := {}:

Blimit := 25000:


`run/put` := proc()
  put(args);
  tprint(`Put: `); map(`run/put/print`, [args]);
  if `storing/b` then store(`store/file`) fi
end:

miniprint := proc(p)
  option inline;
  printf("%q\n\n", p)
end:

microprint := proc(p)
  option inline;
  `if`(evalb(length (p) > 1000), print(lhs(p)='`Too large object in`'(indets(rhs(p)))), miniprint(p));
end:

smartprint := proc(p)
  option inline;
  `if`(evalb(length (p) > 300),  microprint(p), print(p));
end:

`run/put/print` := op(smartprint):


pds := proc()
  op(map(`pds/1`, op(2,op(`pd/tab`))))
end:

`pds/1` :=  proc(p)
   op(map(
     proc(e,f) 
       'pd'(f,op(1,e)) = op(2,e) 
     end, op(2,op(2,p)), op(1,p))) 
end:


`store/pds` := proc(fd)
  # HB:
  global `pd/tab`;
  local p,el,e,f,b; 
  reduce(); b := false;
  for p in op(2,op(`pd/tab`)) do
    el := op(2,op(2,p));
    f := op(1,p);
    for e in el do
      if b then fprintf(fd, ",\n") else b := true fi; 
      fprintf(fd, "  pd(%a, %a) = %a", f,op(1,e), op(2,e));
    od
  od
  # :HB
end:

store := proc(file)
  # HB: 
  local fd;
  print(cat(`storing in `, file));
  if nargs = 0 then 
    # storing in terminal
    error "Sorry, storing in terminal not implemented yet."; # TODO: implement it
  else
    # storing in file
    fd := fopen(file, WRITE, TEXT):
    try
      fprintf(fd, "dependence(%q);\n\n", dependence());
        
      map(e->fprintf(fd, "put(%q);\n", e), [`unks/assignments`()]);
      fprintf(fd, "\n");
  
      fprintf(fd, "put(\n");
      `store/pds`(fd);
      fprintf(fd, "\n);\n");
      
      fprintf(fd,"nonzero(%q);\n\n", op(nonzero()));

      # TODO: Varodering must be stored here
     
      #fprintf(fd,"\n# RESOLVE=%a\n",RESOLVE); # store also RESOLVE var as a comment
      #cannot be here, becouse when RESOLVE is too long, is printed to several lines 
      #(but only the first one begins with # what causes syntax error when reading later)
    finally
      fclose(fd);
    end;
  fi
  # :HB
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

ressize := 1000:
putsize := 200:
maxsize := 100:

`run/time` := time():
`run/bytes` := kernelopts(bytesalloc):
`derive/time` := 0.0:


#`derive/seq` := Threads[Seq]: #TODO:

derive := proc()
  local a, ans, time0;
  global `derive/tab`,`derive/pd/tab`,`noderive/s`, `derive/time`;
  time0 := time();
  for a in [args] do
    if not assigned(`derive/tab`[a,1]) then 
      `derive/tab`[a,1] := `vars/1`(a) minus `noderive/s`
    fi;
    if not assigned(`derive/pd/tab`[a,1]) then 
      `derive/pd/tab`[a,1] := a
    fi
  od;
  ans := seq(`derive/1`(a,1), a = [args]);
  inc(`derive/time`, time()-time0);
  return(ans);
end:

noderives := proc()
  global `noderive/s`,`b/var/s`;
  `noderive/s` := {args} union `b/var/s`
end:

noderives():

`derive/1` := proc(a,c)
  local ds,us,ps,p,aux,t,ns,s,b,rt,lb, vs, Vs, cs, M;
  global `derive/tab`,`derive/pd/tab`, `derive/depth`;
  rt := `report/tab`[derive]; lb := `DERIVE:`;
  if rt > 1 then report(lb,['procname', `input arg1:`, LVar(a)=size(a), `arg2`, c]) fi;
  if rt > 4 then report(lb,['procname', `input arguments:`, a,c]) fi;
  if rt > 3 then report(lb,[`expression:`, `derive/pd/tab`[a,c]]) fi;
  if assigned(`derive/depth`) and `count/length`(c) > `derive/depth` then
    if rt > 3 then report(lb,[`evalTD forced by derive/depth, length is :`, `count/length`(c)]) fi;
    RETURN(Simpl(evalTD(`derive/pd/tab`[a,c])))
  fi;
  ds := `derive/tab`[a,c];
  if rt > 3 then report(lb,[`variables:`, op(ds)]) fi;
  if nargs > 2 then us := args[3] intersect ds;
    if rt > 3 then report(lb,[`usable variables:`, op(us)]) fi    
  else us := ds
  fi;
  # HB:
  # deal with some special types of a - try to estimate what are good directions
  vs := convert(us,list); # vars of a
  ## polynomial
  #aux := select(v -> type(a, polynom(anything,v)), vs); # polynomial vars
  #if nops(aux) > 0 and nops(aux) < nops(us) then
  #  if rt > 1 then report(lb,[`Deriving polynom, reducing usable variables`, op(us), `to`, op(aux)]) fi;    
  #  us := convert(aux,set);
  ## sum
  #elif type(a, `+`) then
  #   Vs := MaP(`vars/1`@Vars, convert(a,list)); # vars of unknowns in subitems
  #   cs := map(v -> nops(select(`=`, map(has,Vs, v), true)), vs); # count occurrences of vars in subitems
  #   M := min(cs);
  #   aux := zip((v,c)-> if c<=M then v fi , vs, cs); # vs :=  'nice' vars
  #   if nops(aux) > 0 and nops(aux) < nops(us) then
  #     if rt > 1 then report(lb,[`Deriving sum, reducing usable variables`, op(us), `to`, op(aux)]) fi;    
  #     us := convert(aux,set);
  #   fi
  #fi;
  if rt > 5 then report(lb,[`us`,us]) fi;    
  # :HB
  ns := us;  # just anything nonempty if us nonempty
  while ns <> {} do
    ps := `remove/vars/<`(us,us);  # top vars
    if rt > 5 then report(lb,[`ps:`, ps]) fi;    
    aux := [seq(p = `derive/pd`(a,c,p), p = ps)];  # [p = pd(a,p), ...]
    aux := select(proc(e) op(2,e) <> 0 end, aux);  # select pd <> 0
    if rt > 5 then report(lb,[`aux selected:`, aux]) fi;
    ns := ps minus map(proc(e) op(1,e) end, {op(aux)});  # top, but pd = 0
    if rt > 5 then report(lb,[`ns:`, ns]) fi;  
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
  if rt > 5 then report(lb,[`aux:`, aux]) fi;  
  aux := [seq([op(p),size(op(2,p))], p = aux)];  # [[p, pd(a,p), size], ...]
# aux := sort(aux, proc(t1,t2) evalb(op(3,t1) < op(3,t2)) end);  # sort by size
  s := size(`derive/pd/tab`[a,c]);
  if rt > 3 then report(lb,[`current size:`, s]) fi;
  aux := select(proc(t,s) op(3,t) < s end, aux, s);  # select < a
  if aux = [] then if rt > 3 then report(lb,`none makes less`) fi; 
    if rt > 2 then report(lb,[`derivation finished`, a,c]) fi;
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
  local ans,rt,lb,e;
  global `derive/pd/tab`;
  rt := `report/tab`[derive]: lb := `DERIVE:`;
  if assigned(`derive/pd/tab`[a,c*q]) then 
    ans := Simpl(evalTD(`derive/pd/tab`[a,c*q]))
  elif assigned(`derive/pd/tab`[a,c]) then
    if rt > 3 then report(lb,[`actually deriving;`, q]) fi;
    if rt > 4 then report(lb,[`actually deriving`, VarL(`derive/pd/tab`[a,c]),`by`,q]) fi;
    ans := Simpl(evalTD(pd(`derive/pd/tab`[a,c],q)))
  else ERROR (`this should not happen`)
  fi;
   if rt > 4 then 
     try
       report(lb,[`actually derived`, [LVar(a),c,q]]);
       report(lb,[`with result`, [size(ans),VarL(ans)]]);       
     catch:
        e := lastexception;
        printf("\nPROBLEM (is radnormal used in simpl? maybe that is  bug #3 described in http://www.mapleprimes.com/posts/101122-Possible-Maple-Bugs-I-Found-Blog): %q\n", 
           StringTools[FormatMessage](e[2..-1]));   
        printf("Derived:\na=%a\nc=%a\nq=%a\nans=%a\n\n", a,c,q,ans);  
        error ;
     end:
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

`resolve/normalizer` := op(normal):
`resolve/time` := 0.0:

#`resolve/nonresrat` := 3;

resolve := proc()
  global `resolve/normalizer`, `resolve/time`;
  local res, time0 := time();
  res := `resolve/1`(op(map(`resolve/normalizer`,{args})));
  inc(`resolve/time`, time()-time0);
  return (res);
end:

$ifndef jets_new_resolve_enable

#
#  R e s o l v e - the old implementation
#


`resolve/1` := proc()
  local as,bs,vl,i,rt,lb;
  lb := `RESOLVE:`; rt := `report/tab`[resolve];
  as := map(numer,{args}) minus {0};
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

`resolve/lin` := proc(as,vl)
  local bs,v,cs,ls,ps,p,q,qs,ans,aux,rs,rt,lb;
  global maxsize, RESOLVE, `resolve/result/suppressedminsize`;
  `resolve/result/suppressedminsize` := NULL;
  
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
    if aux <> {} then lprint(`There are`, nops(aux),`suppressed solutions of sizes:`, op(map(size,aux)));
        `resolve/result/suppressedminsize` := min(op(map(size,aux))); # HB
    else
       `resolve/result/suppressedminsize` := NULL : # HB
    fi;
    # HB: store what failed to the global variable RESOLVE
    RESOLVE := map(
      proc(r) 
        if type(op(1,r), linear(op(2,r))) then 
          tprint(`linear resolving failed for`, op(2,r));
          print (coeff(op(r),1)*op(2,r) = -coeff(op(r),0));
          [coeff(op(r),1), op(2,r), -coeff(op(r),0)] # [a1,x1,-b1] FAIL prvního druhu
        else 
          tprint(`resolving failed for`, op(2,r), `nonlinear `);
          print (op(1,r));
          [op(1,r), op(2,r)] # [a,x1] FAIL druhého druhu
        fi
      end, rs);
    # :HB
    FAIL
  else op(ans)
  fi;
end:


$else

#
#  R e s o l v e - the new implementation (not well tested yet)
#

printf("\nUsing the new implementation of resolve (nod well tested yet!)\n");


#`resolve/nonresrat` := 3;

`resolve/1` := proc()
  local as,bs,as1, as2, cs,  ds, vl,i,rt,lb,ans, A, AL, AN, A1, A0, A1S, A1H, B, ff;
  global `resolve/nonresrat`;
  lb := `RESOLVE:`; rt := `report/tab`[resolve];
  if rt > 0 then report(lb,cat(`input `, nops([args]))) fi;   
  as := MaP(numer,{args}) minus {0};
  if rt > 1 then report(lb,cat(`numer `, nops(as))) fi; 
  as := MaP(divideout, as)  minus {0}; # remove nonzero factors
  if rt > 1 then report(lb,cat(`divideout `, nops(as))) fi; 
  bs := select(type, as, nonzero);
  if rt > 3 then report(lb,cat(`contradictory `, nops(bs), ` eqns `), bs) fi; 
  if bs <> {} then print(op(map(proc(b) b = 0 end, bs)));
    ERROR(`there are contradictory equations`)
  fi;
  
  #as := MaP(Simpl,as);
  #if rt > 1 then report(lb,cat(`Simpl `, nops(as))) fi; 
  as := MaP(reduceprod,as) minus {0};  
  if rt > 1 then report(lb,cat(`reduceprod `, nops(as))) fi; 
  
  A := MaP(proc(b) 
              local a, V, V1, LC, LV, r,s, Cs, Ms;
              V := VarL(b);
              if nops(V)=0 then # no unknowns
                a := Simpl(b);
                tprint("No unknowns in ", a);
                return NULL;
              fi;
              V1 := V[1];
              a := Simpl(b, [V1]);
              #if not(frontend(ispoly, [a, linear, V1, 'r', 'LC'])) then  # nonlinear or non-polynomial case              
              if not(type(a, linear(V1))) then  # nonlinear or non-polynomial case
                if rt > 5 then printf("Nonlinear case, expr=%a, VarL=%a, LC=%a\n",a,V,LC); fi;
                assert([not(type(a, linear(V1))), 
                      "Implementation error, failed to compute leading coeff (in VarL %a) of linear expression %a", 
                      V,a], callstackskip=1);
                return compat[Record[packed]]('expr'=a, 'Vars'=V, 
                                      'price'=infinity, 
                                      'size'=size(a),
                                      #'coeffs'=[C], 'monoms'=[M],
                                      'leadLinCoeff'=FAIL,
                                      'leadLinCoeffVars'=FAIL)
                                      #'rest'=a,
                                      #'subs'=FAIL
              else # linear case
                LC := coeff(a, V1);
                assert([type(a, linear(V1)), 
                        "Implementation error, found leading coeff %a (in VarL %a) of nonlinear expression %a", 
                        LC, V, a], callstackskip=1);
                LC := collect(LC, V, simpl, distributed);
                #r := collect(a-LC*V1, V, simpl, distributed);
                #s := collect(-r/LC, V, simpl, distributed);
                LV := Vars(LC);
                return compat[Record[packed]]('expr'=a, 'Vars'=V, 
                                      'price'=`resolve/lin/price`(a), 
                                      'size'=size(a),
                                      #'coeffs'=[C], 'monoms'=[M],
                                      'leadLinCoeff'=LC,
                                      'leadLinCoeffVars'=LV)
                                      #'rest'=r,
                                      #'subs'=s 
              fi
            end, 
            convert(as,list));
  A := sizesort(A, a->a:-price);
  AN, AL := selectremove(a->a:-leadLinCoeff in {0, FAIL}, A); # nonlin, lin
  A1, A0 := selectremove(a->type(a:-leadLinCoeff,nonzero), AL); # resolvable, nonresolvable
  A1S, A1H := selectremove( a -> (nops(a:-Vars)<=1) # simple, hard 
                            # or a:-rest=0 or type(a:-subs, monomial(constant, a:-Vars))
                            #a->a:-price<2 
                            #or type(a:-leadLinCoeff, numeric) or a:-leadLinCoeffVars={} 
                            , A1);

  if rt > 1 then report(lb, sprintf("There are %a linear resolvable (%a simple and %a hard),"
                            " %a linear NONresolvable and %a NONlinear eqs. Prices and sizes are:\n"
                            "LIN. RESolv.: %a,\nLIN. NONresolv: %a;\nNONLIN: %a.\n", 
                            nops(A1), nops(A1S), nops(A1H), nops(A0), nops(AN), 
                            map(a->[a:-price,a:-size], A1), 
                            map(a->[a:-price,a:-size], A0), 
                            map(a->[a:-price,a:-size], AN))) fi; 
  if rt > 2 then report(lb, `if`(nops(A1)>0, 
                                 sprintf("Linear resolvable eqs properties are [price, size, VarL, LeadLinCoeff]:\n%s",
                                    StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-Vars, a:-leadLinCoeff]), A1))),
                                 "No linear resolvable equation found.")) fi; 
  if rt > 3 or (rt > 2 and nops(A1)=0) then 
                 report(lb, cat("Linear NONresolvable eqs properties are [price, size, VarL, LeadLinCoeff]:\n%s",
                                "NONlinear eqs properties are [price, size, Vars]:\n%s"), 
                            StringTools:-Join(map(a -> sprintf("%q\n",[a:-price, a:-size, a:-Vars, a:-leadLinCoeff]), A0)),
                            StringTools:-Join(map(a -> sprintf("%q\n",[a:-price, a:-size, a:-Vars]), AN))) fi; 
  if rt > 4 then report(lb, `if`(nops(A1)>0, 
                                 sprintf("LIN RESolvable eqs [price, size, eq, leadVar]:\n%s"
                                         "LIN NONresolvable eqs [price, size, eq, leadVar]:\n%s",
                                         StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-expr,a:-Vars[1]]), A1)),
                                         StringTools:-Join(map(a -> sprintf("%q\n",[a:-price,a:-size,a:-expr,a:-Vars[1]]), A0))),
                                 "")) fi;                             
  
#DoReports(resolve,  [op(map(a->a:-expr,A1)), op(map(a->a:-expr,A0)),  op(map(a->a:-expr,AN))], 
#     comment=cat(sprintf(" resolve input (#lin resolvable: %a (%a of them simple), #lin non-res.: %a #nonlin: %a):\n", 
#				nops(A1), nops(A1S), nops(A0), nops(AN)), 
#       sprintf("# prices(res-lin)=%q\n", map(a->a:-price, A1)),
#       sprintf("# sizes(res-lin) =%q\n", map(a->a:-size, A1)),
#       sprintf("# LVars(res-lin)=%q\n", map(a->a:-Vars[1], A1)),
#       
#       sprintf("# prices(nonres-lin)=%q\n", map(a->a:-price, A0)),
#       sprintf("# sizes(nonres-lin) =%q\n", map(a->a:-size, A0)),
#       sprintf("# LVars(nonres-lin)=%q\n", map(a->a:-Vars[1], A0)),
#       
#       sprintf("# prices(nonlin)=%q\n", map(a->a:-price, AN)),
#       sprintf("# sizes(nonlin) =%q\n", map(a->a:-size, AN)),
#       sprintf("# LVars(nonlin)=%q\n", map(a->a:-Vars[1], AN))));
    
  if nops(A1) = 0 then
    `resolve/fail`(AL,AN);  
    #print("OLD FASHION RESOLVE failure handling");
    B := A;
  #####                                                  
  else 
    B := A1S; # all simple
    if nops(B)=0 and nops(A1H)>0 then B:= [op(B), A1H[1]] fi; # no simple, take 1 hard (if exists) 
    #if nops(A1H)>0 then B:= [op(B), A1H[1]] fi; # all simple and 1 hard (if exists)  
  fi; ####
  #map(lprint@lprint, AL);lprint(); map(lprint@lprint, AN);
  

  if assigned(`resolve/nonresrat`) and nops(A1)>0 and nops(A0)>0 
    and A1[1]:-price>A0[1]:-price*`resolve/nonresrat` then
    ff := true;     
    B := [A0[1]];
    #B := AL;  
    printf("Forcing linear failure:\n"
       "Resolvable expression of price %a and size %a"
       " overlapped nonresolvable expression price %a and size %a (`resolve/nonresrat`=%a).\n",
     A1[1]:-price,  A1[1]:-size, A0[1]:-price,  A0[1]:-size,  `resolve/nonresrat` );
    #printf("All %a expressions (including %a resolvable) are considered as nonresolvable.\n", nops(B), nops(A1));
    printf("Of all %a expressions (including %a resolvable), first one choosen to be resolved.\n", nops(B), nops(A1));
  else
    ff := false;
  fi;
  
  vl := ListTools:-Reverse(sort([op(`union`(op(map(a -> convert(a:-Vars,set), B))))],  `Vars/<<`)); # present Vars in resolvable eqs.
  if vl = [] then ERROR(`no unknowns`, as) fi;  cs := map(a -> a:-expr, B);
  
  DoReports(resolve, cs,comment=cat(" resolve selection:\n", 
       sprintf("# prices=%q\n", map(a->a:-price, B)),
       sprintf("# sizes =%q\n", map(size, B)),
       sprintf("# LVars=%q\n", map(a->a:-Vars[1], B))));  
  
  ans := `resolve/lin`(convert(cs,set), vl, ForceFail=ff);
  
  DoReports(resolve, [ans],comment=" resolve output");
  return (ans);
  #####fi;
end:

`resolve/lin/price` := proc(r)  option inline; size(r) end:

`resolve/fail` := proc(AL, AN)
  #map(`resolve/fail/report/lin`, AL);
  #map(`resolve/fail/report/nonlin`, AN);
  tprint(sprintf("Resolve failed (%a linear, %a NONlinear).", nops(AL), nops(AN)));  
  FAIL;
end:

`resolve/fail/report/lin` := proc(a)
  tprint(sprintf("Linear resolving failed in %a:", a:-Vars[1]));
  #print(a:-expr);
  print(a:-leadLinCoeff*a:-Vars[1]=-a:-rest);
end:

`resolve/fail/report/nonlin` := proc(a)
  tprint(sprintf("NONLinear resolving failed in %a:", a:-Vars[1]));
  print(a:-expr);
end:

`resolve/lin` := proc(as,vl,{ForceFail::truefalse:=false})
  local bs,v,cs,ls,ps,p,q,qs,ans,aux,rs,rt,lb;
  global maxsize, RESOLVE, `resolve/result/suppressedminsize`;
  `resolve/result/suppressedminsize` := NULL;
  
  lb := `RESOLVE:`; rt := `report/tab`[resolve];
  bs := map(Simpl, as, vl);
  if rt > 2 then report(lb,cat(`resolving `, nops(bs),` eq.`)) fi; 
  bs := remove(proc(a) evalb(a = 0) end, bs);  # remove zero eqs.
  if rt > 2 then report(lb,cat(nops(bs), ` eq. nonzero`)) fi; 
  if bs = {} then RETURN () fi;  # no eq.
  ans := {}; rs := {}; 
  # Correction: rvl removed 12.7.2007
  for v in vl do # for v running through all Vars in reverse Varordering
    if rt > 4 then report(lb,`resolving with respect to`, v) fi; 
    bs := map(divideout, bs); # remove nonzero factors
    bs := map(Simpl, bs, vl); # Simplify
    bs := remove(proc(a) evalb(a = 0) end, bs);  # remove zero eqs.
    bs := map(reduceprod, bs);  # reduce products
    cs := select(has, bs, v);  # cs = subset of bs with v 
    if rt > 4 then report(lb,`resolving equations:`, cs) fi; 
    bs := bs minus cs;  # bs = subset without v
    ls := select(type, cs, linear(v));  # ls = subset of cs linear in v
    if rt > 4 then report(lb,`of them linear:`, ls) fi; 
    if ForceFail=false then
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
    else
      printf("Enforced linear failure (w. r. to %a).\n", v);
      rs := rs union map(proc(a,v) [a,v] end, cs, v)  # move cs to rs
    fi;
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
    if aux <> {} then lprint(`There are`, nops(aux),`suppressed solutions of sizes:`, op(map(size,aux)));
        `resolve/result/suppressedminsize` := min(op(map(size,aux))); # HB
    else
       `resolve/result/suppressedminsize` := NULL : # HB
    fi;
    # HB: store what failed to the global variable RESOLVE
    RESOLVE := map(
      proc(r) 
        if type(op(1,r), linear(op(2,r))) then 
          tprint(`linear resolving failed for`, op(2,r));
          print (coeff(op(r),1)*op(2,r) = -coeff(op(r),0));
          [coeff(op(r),1), op(2,r), -coeff(op(r),0)] # [a1,x1,-b1] FAIL prvn’ho druhu
        else 
          tprint(`resolving failed for`, op(2,r), `nonlinear `);
          print (op(1,r));
          [op(1,r), op(2,r)] # [a,x1] FAIL druhŽho druhu
        fi
      end, rs);
    # :HB
    FAIL
  else op(ans)
  fi;
end:

reporters[resolve]:= []:  # no reporting by default
 
AddReporter[resolve] := proc({mode:=incremental, incProc:=`run/getstep`, 
                              handler::name:=default, handlerOpts:=NULL})
  global reporters;
  local r;
  r := CreateDataReporter(args,_options, 
                          ':-outputProc'=`resolve/reporter`, 
                          addOutArgs=(':-handler'=handler, ':-handlerOpts'=handlerOpts));
  reporters[resolve] := [op(reporters[resolve]), r];
end:

`resolve/reporter`:= proc(as,{handler:=default}) # may be used
  local H, hopts, n := 0;
  #printf("Resolving %a expressions (step %a)...\n",nops(as), `run/getstep`());
  if type(handler, indexed) then 
    H := cat(`resolve/reporter/`,op(0,handler)); hopts := op(handler) 
  else 
    H := cat(`resolve/reporter/`,handler) ; hopts := NULL 
  fi;
  cat(op(map(H, as, proc() n := n+1 end, hopts)));
  #printf("(end of resolving step %a).\n", `run/getstep`());
  end:

`resolve/reporter/default` := proc(a, N, {collectFun:=`reporter/CF/id`})
 # [N,i]=[Var=[length,vars], ...]
 local vs, c, e;
 try
   vs := VarL(a);
   c := collect(a, vs, collectFun, distributed);
   #c := polynomMOSortL(a, CF=collectFun);
   sprintf("[%a,%a,%a]=%q\n", `run/getstep`(), N(), size(a), c);
  catch:
    e := lastexception;
    print(e);
    cat(StringTools[FormatMessage](e[2..-1]), " original expression: ", convert(a,string));
  end try;
end:

`reporter/CF/id` := proc(e) e end:

`reporter/CF/X` := proc(e) X[e] end:

`reporter/CF/L` := proc(e)
  local L := length(e);
  if L <= 5 then e
  else [length(e)] fi;
end:

`reporter/CF/Lv` := proc(e)
  local L := length(e);
  if L <= 5 then e
  else [length(e),vars(e)] fi;
end:

coeffsV := proc(F, {CF::{procedure,name}:=proc(x) option inline; x end})
  description "collects a given polynomial and returns list of coefficients and list of monomials"
               "keyword CF may specify a collecting function (applied to coefficients)";
  local f, vs, k, l ;
  vs := Vars(F);
  f := collect(F, vs, CF, distributed);
  k := coeffs(f, vs, l); 
  [k],[l];
end:


#polynomMOSortL := proc(F)
#  description "Sorts polynomial using monomial order `Vars/<<` "
#              "and returns a (sorted) list of its terms"
#              "keyword CF may specify a collecting function (applied to coefficients)";
#  # polynomials in maple cannot be sorted by user-defined ordering  so list must be returned
#  local K, L, S, R;
#  K, L := coeffsV(_passed,_options);
#  S := table(zip(`=`,L,K));
#  R := sort(L, (a,b)->`Vars/<<`(a,b));
#  map(a->S[a]*a, R);
#end:
#
#polynomMOSortCM := proc(F)
#  description "Sorts polynomial using monomial order `Vars/<<` "
#              "and returns a pair of (sorted) lists: coefficients and monomials"
#              "keyword CF may specify a collecting function (applied to coefficients)";
#  # polynomials in maple cannot be sorted by user-defined ordering  so list must be returned
#  local K, L, S, R;
#  K, L := coeffsV(_passed,_options);
#  S := table(zip(`=`,L,K));
#  R := sort(L, (a,b)->`Vars/<<`(a,b));
#  map(a->S[a], R), R;
#end:

$endif

# Resolve - the common part

`type/nounks` := proc(a) evalb(unks(a) = {}) end:

`type/resolv` := proc(x)
  evalb(`vars/1`(a) minus `union`(op(map(`vars/1`,unks(a)))) = {})
end:

`resolve/lin/1` := proc(p,v) -coeff(p,v,0)/coeff(p,v,1) end:

`resolve/subs` := proc(a,v,q)
  Simpl(subs(v = q, a)) # Correction: Simpl added 9.7.2007
end:

`type/resolvable` := proc(a)
  if unks(a) <> {} and
    `vars/1`(a) minus `union`(op(map(`vars/1`,unks(a)))) = {} then false
  else true
  fi
end:


#
#   V a r s
#

Vars := proc(a)
  global `unk/s`;
  if nargs > 1 then error "Too many arguments" # `union`(op(map(procname, {args})))
  elif type (a,{'constant','ar'}) then {}
  elif type(a, {sequential,array}) then `union`(op(map(procname, convert(a,set))))
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

Varl := proc()
  description "an unsorted list of Vars";
  convert(Vars(args),list);
end:

VarL := proc()
  description "list of Vars sorted by current Varordering, maximal element is first";
   ListTools:-Reverse(sort(Varl(args),  `Vars/<<`));
end:

LVar := proc()
  description "Leading Var w.r. to current Varordering";
  local vs;
  vs := Varl(args);
  if nops(vs) = 0 then {}
  else ListTools[FindMaximalElement](vs,  `Vars/<<`) fi;
end:

`Vars/TD` := proc(f,x)
  option remember;
  if type (x,'name') then
      `union`(op(map(`Vars/TD/0`, `vars/1`(f), f, x)))
    union
      `union`(op(map(`Vars/TD/1`,`vars/1`(f),x)))
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
    `nonzero/s` := map(factor@numer@simpl,`nonzero/s`) # M.M. bugfix 18.5.2012
  else `nonzero/s` := map(factor@numer@simpl,{args}) # M.M. bugfix 18.5.2012
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
  #if unks(a) = {} and a <> 0 then NULL elif # Bug fix 25. 04. 2008
  if type (a,`^`) then
    if type (op(2,a), rational) and op(2,a) > 0 then procname(op(1,a))
    else a
    fi
  elif type (a,`*`) then op(map(procname,[op(a)]))
  else a
  fi
end:

# Dividing out nonzero factors.
# An expression is nonzero if either declared nonzero or different
# from zero for all values of unknowns 
# M.M. 2008

divideout := proc(a)
  local ns;
  if nargs = 1 then ns := `nonzero/s` else ns := args[2] fi;
  `divideout/nonzero`(`divideout/unks`(factor(Simpl(a))), ns) # Correction: Simpl added 9.7.2004
end:

`divideout/unks` := proc(a)  # treats explicit products and powers
 if a = 0 then 0
 elif type (a, `divideout`) then 1
 elif type (a,`*`) then map(procname,a)
 elif type (a,`^`) then
   if type (op(2,a), positive) then procname(op(1,a)) else a fi # H.B. 2004
 else `divideout/unks/1`(a)
 fi
end:

# `type/divideout` := {specfunc(anything,exp)}: 
`type/divideout` := proc(a) # HB 14. 5. 2008
  if type(a, positive) then true
  elif type(a, specop(anything, `+`))  
    or type(a, specop(anything, `*`)) then
    andmap(type, [op(a)],  divideout)
  elif type(a, specfunc(anything,exp)) then true
  elif type (a,`^`) and type (op(2,a), positive) and type (op(1,a), divideout) then true # H.B. 30. 11. 2011
  else
    false
  fi
end:

`divideout/unks/1` := proc(a)
  local us,vs,aux, cs, v1, v2;
  us := unks(a);
  if unks(a) = {} then return 1 fi;
  # MM  vs := `vars/1`(a, noWarn) minus vars(op(us), noWarn);
  # HB:
  v1 := `vars/1`(a, noWarn) ;
  v2 := select(e -> type(a, polynom(anything, e)), v1);
  vs := v2 minus vars(op(us), noWarn);
  #DOE(if v1 <> v2 then lprint('procname', v1<>v2, a) fi);
  # :HB
  if vs = {} then a # presumably a = 0 can have a solution
  elif type(a, polynom(anything,vs)) then
    aux := collect(a, vs, distributed, simpl);
    cs := coeffs(aux, vs);
    if ormap(type, [cs], nonzero) then 1
    else a # all coeffs can be zero
    fi
  else a # does not know
  fi
end:

`divideout/normalizer` := op(normal):

`divideout/nonzero` := proc(a,ns)  # divides elements of ns out of a
  local f,g,h;
  g := `divideout/normalizer`(a);
  for f in ns do h := `divideout/normalizer`(g/f);
    while `divideout/size`(h) < `divideout/size`(g) do
      g := h; h := `divideout/normalizer`(g/f);
    od
  od;
  if type (g,'constant') then if g = 0 then 0 else 1 fi else g fi # H.B. 2004
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

`type/nonzero` := proc (a) 
  local b; global NONZERO, ZERO;
  b := evalb(divideout(numer(simpl(a))) = 1);
  #if b then NONZERO := NONZERO union {a}
  #else ZERO := ZERO union {a}
  #fi;
  b
end:

NONZERO := {}:
ZERO := {}:

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
  local i,t,s; 
  appendto (reportfile);
  printf("%s <%a, %a> ", convert(lb,string), floor(time() - `run/time`), Bytes()); # HB
  if type(text,name) then printf("%s %q", args[2..-1]);
  elif type(text, string) then printf(args[2..-1]);
  #elif type(text,list) then map(t->printf(" %s", convert(t,string)), text)
  else  printf("%q", op(text))
  fi;
  printf("\n\n");
  writeto (terminal); NULL
end:

`report/tab`[derive] := 0:
`report/tab`[resolve] := 0:
`report/tab`[run] := 0:
`report/tab`[cc] := 0:
`report/tab`[pd] := 0:
`report/tab`[nonzero] := 0: # HB

lb := NULL:

tprint := proc() printf("[%a] <%a> %s %q\n", `run/getstep`(), floor(time() - `run/time`),  args) end: # HB

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
  local x1,x2,u1,u2,o,pars;
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
    if type(o,function) then pars := op(o); o := op(0,o) else  pars := NULL fi;
    if not Existing(`Vars/<</`,o) then ERROR (`invalid option`, o) fi;
    if Call(`Vars/<</`,o)(u1,x1,u2,x2,pars) then RETURN (true) fi;
    if Call(`Vars/<</`,o)(u2,x2,u1,x1,pars) then RETURN (false) fi 
  od;
  false
end:

`Vars/<</params` := proc(u1,x1,u2,x2,Fs)
  local pars, uu, o;
  pars := args[6..-1];
  if u1 in Fs then
    if u2 in Fs then
      for o in pars do 
        if not Existing(`Vars/<</`,o) then ERROR (`invalid option`, o) fi;
        if Call(`Vars/<</`,o)(u1,x1,u2,x2) then RETURN (true) fi;
        if Call(`Vars/<</`,o)(u2,x2,u1,x1) then RETURN (false) fi 
      od
    else RETURN(true)
    fi
  elif u2 in Fs then RETURN(false)
  else RETURN (FAIL)
  fi;
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
    yl := [op(`vars/1`(x))];
    yl := sort(yl,`vars/<<`);
    y := op(nops(yl), yl); 
    member(y, [op(`vars/1`(`transform/count`(x)))])
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
    yl := [op(`vars/1`(x))];
    yl := sort(yl,`vars/<<`);
    y := op(1, yl);
    member(y, [op(`vars/1`(`transform/count`(x)))])
  else ERROR (`not a count`, x)
  fi 
end:

`Vars/<</revdeg` := proc(u1,x1,u2,x2)
  `Vars/<</rd/1`(x2/x1);
end:
 
`Vars/<</rd/1` := proc(x)
  local y;
  y := convert(`vars/1`(x),`*`)^degree(x)/x;
  return degree(y)>0;
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
  if nops(aux1) = 0 then return ;# HB: Bug fix
  elif nops(aux1) > 1 then aux1 := aux1[1..2] fi;
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


TestUnkOrd := proc(L::list:=select(type, `unk/<</list`, symbol))
  description 
    "Simple test of correctness of unknowns ordering selected based on the dependece sets"
    "(it is just a very basic guess so the result is just a recommendation)";
  global `unk/<</list`;
  local i, j, r, T, s;
  try
    # vars: dependences vs. unknowns ordering
    r := {seq(seq(`TestUnkOrd/vars`(L[i], L[j]), j=i+1..nops(L)), i=1..nops(L)-1)};
    r := ListTools:-Reverse(sort(convert(r, list), `Vars/<<`));
    if nops(r)>0 then 
      WARNING("suspicious unknowns ordering found in variables %1", r) 
    fi;
    # dependences in pd/tab
    T := `cc/pd/listall`();
    s := select(U -> assigned(`pd/tab`[U]) and (T[U] minus {indices(`pd/tab`[U], nolist)} <> {}), L);
    if nops(s)>0 then 
      WARNING ("suspicious `pd/tab` dependences %1:", s);
      map(proc(U)  
            printf("Unknown %a: vars(%a) = %a but:\n", U, U, vars(U));
            map(proc(m) local vs := vars(`pd/tab`[U][m]);
                  if not(vs subset vars(U)) then printf("  pd(%a,%a):  vars = %a,   Vars = %a\n",  
                                                         U, m, vs, Vars(`pd/tab`[U][m])) fi;
                end, [indices(`pd/tab`[U], nolist)]);
          end, s);
    fi;
    # the result
    return r, s;
  catch:
    printf("TestUnkord failed: %q\n", 
           StringTools[FormatMessage](lastexception[2..-1]))
  end;
end:

`TestUnkOrd/vars` := proc(U, V)
  if not( vars(U) subset vars(V) ) then
    printf("The unknown %a of variables %a is followed by the unknown %a of fewer variables %a\n", 
            U, vars(U), V, vars(V));
    U
  fi;
end:



### ordering of polynomials in Vars

`monom/degree` := proc(a)
  description "";
  # cannot be inlined since recursive
  `if` (type(a,`*`),
     `+`(op(map('procname', convert(a,list)))),
     `if`(type(a, `^`),
          op(2,a),
          1))
end:



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
  else 'apply'(x,f) ## M.M. Sept. 19, 2O12
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
    end, [op(`vars/1`(f) minus `b/var/s`)], v, f), `+`)
end:

# Point symmetries

papply := proc(v,f)
  convert(map(
    proc(q,v,f) 
      if type (q,`b/var`) then coeff(v,pd[q])*pd(f,q)
      elif type (q,`f/var`) then coeff(v,pd[q])*pd(f,q)
      else `papply/j`(op(q),v)*pd(f,q)
      fi
    end, [op(`vars/1`(f))], v, f), `+`)
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
  end, [op(`vars/1` (f) minus `b/var/s`)], f, p), `+`)
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

# Test whether BT is a Backlund transformation  

testBT := proc()
  global `eqn/list`,`n/var/list`,`BT/list`;
  local el;
  el := select(proc(e,n) not member([op(1,e)], n) end, `eqn/list`,`n/lhs/s`);
  op(map(
    proc(e,qs) 
      if member(op(1,[op(1,e)]),`n/var/list`) then NULL
      else Simpl(`convert/TD/1`('jet'(op(1,e)) - op(2,e), qs))
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

#lprint(cat(`Blimit = `,Blimit,
#`  ressize = `,ressize,
#`  putsize = `,putsize,
#`  maxsize = `,maxsize)): 


##############################################################################
### auxiliary
##############################################################################

inc := proc (var::evaln, val := 1 ) assign(var, `if`(type(eval(var),name), 0, eval(var)) + val); end:

# mapmap := proc(f, A, B) 
#   local ff; 
#   ff := rcurry(f, args[4..-1]); 
#   map(a-> op(map(b -> ff(a,b), B)), A) 
# end:
# 
# push := proc(L::uneval, x) L := [op(eval(L)),x] end:
# pop  := proc(L::uneval) local x; x := L[-1]; L := L[1..-2];  x; end:
# 
# 
# CallByOpt := proc(CallByOpt::uneval)
#   # CallByOpt(`function`) 
#   # returns `function/opt/actual_strategy`
#   # where actual_strategy is the value assigned to `function/opt`
#   option inline;
#   cat('CallByOpt', `/opt/`, eval(cat(uneval('CallByOpt'), `/opt`)));
# end:

##############################################################################
# Developer internal notes:
# based on #print(`as of 14 May 2008`);
# Merged with old Jets.s 14. 05. 2008
# print(`26. 6. 2006: derive bugfix revised`);
# print("divideout exp and nonzero polynomials by MM 5. 5. 2008");
# `derive/depth`
##############################################################################







###########################################################################################
###########################################################################################
# JetsCC - sufficient set of compatibility conditions implementation
###########################################################################################
###########################################################################################

# This is an implementation of algorithms based on results published in
#   M. Marvan, Sufficient set of integrability conditions of an orthonomic system. 
#   Foundations of Computational Mathematics 9 (2009) 651-674.

### partial derivatives ###
pd1 := proc (f, ATC(p,{`ar/count`, identical(1)}))
  option inline;
  `if`(p=1, f, pd(f,p))
end:

### jcounts ###

# Jcount is a count in jet variables, i. e. a product of nonnegative integer powers of symbols and jets
# here jet variables MUST be in J[u,x] format

TypeTools[AddType](Jcount,  proc(m) option inline; type(m,monomial) and m<>1 end): 
 
TypeTools[AddType](Jcount1, proc(m) option inline; type(m,monomial)  end): 
  
# jetcount is a count in jet variables, i. e. a product of nonnegative integer powers of symbols and jets
# here jet variables MUST be in jet(u,x) format
# this implementation is VERY slow
  
TypeTools[AddType](jetcount, 
    proc(m) `if`( type(m, `*`),  andmap(`jetcount/not1`, [op(m)]), `jetcount/not1`(m) ) end):

TypeTools[AddType](jetcount1, 
    proc(m) `if`( type(m, `*`),  andmap(`jetcount/1`, [op(m)]), `jetcount/1`(m) ) end):

`jetcount/1` := proc(s) option inline; `if` (type(s,`^`),  type(op(2,s), posint), true) end:
`jetcount/not1` := proc(s) option inline; `jetcount/1`(s) and  s<>1 end:


### jet variables implementation conversions ###

# jet(u,x) to J[u,x]

j2J := proc()
  description "Converts jet(u,x) to J[u,x]";
	eval(args, jet = j2JE);
end:

j2JE := proc(u,x) J[u,x] end:

# J[u,x] to jet(u,x)

J2j := proc()
  description "Converts J[u,x] to jet(u,x)";
	global J2jE;
	eval(args, J = J2jE);
end:

`index/J2jEInd` := proc(Idx,Tbl,Entry)  jet(op(Idx)) end proc:
J2jE := table(J2jEInd):

#
# Fast list operations againts the given 'size' (or price) function
#

# see http://www.mapleprimes.com/blog/joe-riel/sorting-with-attributes

sizesort := proc(ATC(L,list), sizeFun)
  description "Given a list L and size function sizeFun, \
               sorts L by sizeFun sizes of its elements";
  option inline;
  map(attributes,sort(attLBySize(L, sizeFun),`<`));
end proc:

sizemin := proc(ATC(L,list), sizeFun)
  option inline;
  attributes(min(attLBySize(L, sizeFun)));
end proc:

sizemax := proc(ATC(L,list), sizeFun)
  option inline;
  attributes(max(attLBySize(L, sizeFun)));
end proc:

attLBySize := proc(ATC(L,list), sizeFun)::list(complex(float));
  description "Given a list, returns a list of its sizes with original entries as attributes";
  local l;
  [seq](setattribute(HFloat(sizeFun(l)), l), l=L) 
end:


###################################################################################################
# Generalized or improved routines from Jets
###################################################################################################

#
# Dealing with monomials (in jet variables, ie. Jcounts/jetcounts) 
#

# We have two variants of the same routines for different jets implementations

# J[] implementation: In this module, jet variables MUST be in J[u,x] format
module `JetMonomTools/J` ()
  option package; 
  export 
    vars, 
    divide1, divide1f, divideNot1, divideNot1f,
    min, max, rmin, rmax, hull, sets;

  vars := op(indets): # Returns vars of count (fast)

  divideNot1  := proc(u,v,q) option inline; divide(u,v,q) and eval(q)<>1 end:
  divideNot1f := proc(u,v) local q; divide(u,v,q) and q<>1 end: 
  
  divide1  := op(divide): 
  divide1f := op(divide):
  
  min := proc(ATC(S,sequential(Jcount1)), $)
    remove(
      proc(s,S)
        local t;
        for t in S do if divideNot1f(s,t) then RETURN(true) fi; false od
      end, S, S);
  end:
  
  max := proc(ATC(S,sequential(Jcount1)), $)
    remove(
      proc(s,S)
        local t;
        for t in S do if divideNot1f(t,s) then RETURN(true) fi; false od
      end, S, S);
  end:
  
  rmin := proc(ATC(S,sequential(Jcount1)), $)
    selectremove(
      proc(s,S)
        local t;
        for t in S do if divideNot1f(s,t) then RETURN(true) fi; false od
      end, S, S);
  end:
  
  rmax := proc(ATC(S,sequential(Jcount1)), $)
    selectremove(
      proc(s,S)
        local t;
        for t in S do if divideNot1f(t,s) then RETURN(true) fi; false od
      end, S, S);
  end:
      
  hull := proc()
    local M,N,A,MA; 
    M := {args};
    N := {};
    while M <> N do
      N := M;
      for A in M do
        MA := select(proc(B,A) evalb(A intersect B <> {}) end, M, A);
        M := M minus MA union {`union`(op(MA))};
      od
    od; 
    M
  end:
  
  sets := proc(ATC(p,Jcount1), ATC(S,sequential(Jcount1)), $)
    local s,b;
    b := [seq(p/s, s = S)];
    op(map(vars, select(type,b,Jcount)));
  end:
  
end module:


# jet() implementation: In this module, jet variables MUST be in jet(u,x) format
module `JetMonomTools/jet` ()
  option package; 
  export 
    vars,
    divide1, divide1f, divideNot1, divideNot1f,
    min, max, rmin, rmax, hull, sets;

  vars := proc(f) 
    description "Returns vars of count (as fast as possible)"; # still slow
    assert([type(f,count), "%a is not count", f], level=3);
    if type (f,'name') then {f}
    elif type (f,`*`) then `union`(op(map(procname,[op(f)])))
    elif type (f,`^`) then procname(op(1,f))
    elif type (f, specfunc(anything,jet)) then {f}
    else  ERROR (`unexpected object`, f) 
    fi
  end:
  
  divideNot1  := proc(u,v,q::evaln) local qq; qq := u/v; assign(q, qq); type(qq, jetcount) end:
  divideNot1f := proc(u,v) option inline; type(u/v, jetcount) end: 
  
  divide1  := proc(u,v,q::evaln) local qq; qq := u/v; assign(q, qq); qq=1 or type(qq, jetcount) end: 
  divide1f := proc(u,v) option inline; u=v or type(u/v, jetcount)  end:  
  
  min := proc(ATC(S,sequential(jetcount1)), $)
    remove(
      proc(s,S)
        local t;
        for t in S do if divideNot1f(s,t) then RETURN(true) fi; false od
      end, S, S);
  end:
  
  max := proc(ATC(S,sequential(jetcount1)), $)
    remove(
      proc(s,S)
        local t;
        for t in S do if divideNot1f(t,s) then RETURN(true) fi; false od
      end, S, S);
  end:
  
  rmin := proc(ATC(S,sequential(jetcount1)), $)
    selectremove(
      proc(s,S)
        local t;
        for t in S do if divideNot1f(s,t) then RETURN(true) fi; false od
      end, S, S);
  end:
  
  rmax := proc(ATC(S,sequential(jetcount1)), $)
    selectremove(
      proc(s,S)
        local t;
        for t in S do if divideNot1f(t,s) then RETURN(true) fi; false od
      end, S, S);
  end:
      
  hull := proc()
    local M,N,A,MA; 
    M := {args};
    N := {};
    while M <> N do
      N := M;
      for A in M do
        MA := select(proc(B,A) evalb(A intersect B <> {}) end, M, A);
        M := M minus MA union {`union`(op(MA))};
      od
    od; 
    M
  end:
  
  sets := proc(ATC(p,jetcount), ATC(S,sequential(jetcount)), $)
    local s,b;
    b := [seq(p/s, s = S)];
    op(map(vars, select(type,b,jetcount)));
  end:
  
end module:

###################################################################################################
# General (algebraic) cc routines
###################################################################################################

module CC ()
  option package;
  export 
    classess,
    markFF,
    cc,
    init,
    getHS;
  local 
    `cs/H/node`,
    `cs/I`, `cs/I/1`,
    `cs/II`, `cs/II/classes`, 
    `cs/II/hull`,
    `cs/combine`, `cs/combine/1`,
    `cs/H/checktype`,
		 `markFF/2`,
		`cc/attr/priced`,
    `cc/repr/chooser`, 
		`cc/1/attr/ass`, `combinePrices/+`,
		`cc/repr/chooser/1/attr/rhs`,
		`member/CI`,
    stupidSidePrice, `stupidSidePrice/PrintWarning`,
    CI, # the auxiliary symbol for variables of empty direction
    HS, # table of hypergraphs
    rprintf, rlprint;
  
  # uses `JetMonomTools/J`;  
  
  # cc's classess sets are of the form 
  # {p = { class_1, class_2, ... }, q={...}, ...}
  # where p is the monomial where the cc sits
  # and class_i = {m[i,1], m[i,2], ...} consists of monomial(s) from which p can be reached
  # ie. for all i,j exists suitable monomial r[i,j] such that p = r[i,j]*m[i,j]
  # (r[i,j]=1 ie. p=m[i,j] for fist kind cc whereas r[i,j]<>1 for second kind cc)
  TypeTools[AddType](`CC/class`, Jcount=set(set(Jcount1))); 
  
  init := proc()
    rprintf(10, ["CC hypergraph table initialized."]);
    HS := table();
  end:
  
  init();
  
  getHS := proc()
    eval(HS);
  end:
      
  #
  # Generating CC classess sets
  #
    
  classess := proc(ATC(L,sequential(Jcount1)), ATC(H,{table, identical(NULL)}):=NULL, $)::list(`CC/class`);
    description "Returns the minimal set of cc's of givel monomial set L (in the list)";
    local res, H1, R, M;
    if H=NULL then H1 := table() else H1 := H fi; # create temporary table if not given as argument    
    R, M := `JetMonomTools/J`:-rmin(L);
    `cs/I`(L, R, M, H1);
    `cs/II`(L, R, M, H1);
    res := `cs/combine`(L, H1);
    rprintf(3, ["classess(%a)\n =%a.", L, res]);  
    DOE(map(`cs/H/checktype`, [indices(H1, nolist)], H1, level=5));  
    return res;
  end:
  
	`cs/H/node` := proc(u, H, $)
	  description "Returns the node H[u] and creates empty node if H[u] does not exist yet";
	  if not(assigned(H[u])) then 
	    H[u] := [{}, {}, {}];
	  else
     `cs/H/checktype`(u, H);
	    H[u];
	  fi:
	end:
	
	`cs/H/checktype` := proc (u, H, {level::integer:=2}, $)
    assert([assigned(H[u]),
            "Missing hypergraph item H[%a]", u], 
           'level'=level, callstackskip=1),	
    assert([type(H[u], [set,set,set]),
            "Invalid hypergraph item type H[%a]=%q", u, H[u]], 
           'level'=level, callstackskip=1),
    assert([type(H[u][1], set(set(Jcount1))),
            "Invalid hypergraph item [1], H[%a]=%q", u, H[u]], 
           'level'=level, callstackskip=1),
    assert([type(H[u][2], set(set({name, identical(CI)}))),
            "Invalid hypergraph item [2], H[%a]=%q", u, H[u]], 
           'level'=level, callstackskip=1),	  
    assert([andmap(`>`, map(nops, H[u][2]), 0),
            "Invalid hypergraph item [2], there is an empty class, H[%a]=%q", u, H[u]], 
           'level'=level, callstackskip=1),	            
    assert([type(H[u][3], set(Jcount)),
            "Invalid hypergraph item [3], H[%a]=%q", u, H[u]], 
           'level'=level, callstackskip=1);	 
	end:

  `cs/I` := proc(ATC(L,sequential(Jcount1)), ATC(R,set(Jcount)), ATC(M,set(Jcount1)), ATC(H,{table}), $)
    rprintf(6, ["L=%a is R=%a union minimal elements M=%a", L, R, M]);
    map(
      proc(u)
        local res, N, G; 
					G := `cs/H/node`(u, H);
					N := nops(G[1]);
  				if   N=0 then 
  				  res := `cs/I/1`(M, u, H);
  				  H[u][1] := {{u}, res};
  					assert([not(ormap(`member/CI`, G[2])), # 1 must not be member
	        				   "There already is 1 in hypergraph H[%a]=%q.", u, G]); 
	        	H[u][2] := G[2] union {{'CI'}};			  
  				  return u = G[1] 
					elif N=1 then return NULL 
					elif N=2 then return u = G[1] 
					else error "`cs/I`: Wrong hypergraph implementation, H[%1]=[i,ii,M]=%2", u, G;
					fi;
      end, R);   
  end:
		
	`cs/I/1` := proc(M, u, H)::set(Jcount1);
	   local res;
	   res := select((u,v)->`JetMonomTools/J`:-divideNot1f(v,u), M, u);
		 rprintf(5, ["looking for cci: u=%a, M=%a, res=%a, H[%a]=%q", 
									u, M, res, u, H[u]]);
		 res;
	end:
      
  `cs/II` := proc(ATC(L,sequential(Jcount1)), ATC(R,set(Jcount)), ATC(M,set(Jcount1)), ATC(H,{table}), $)
    local C, u, v;
    C := {seq(seq(`if`(u <> v, lcm(u,v), NULL), u=M), v=M)};
    rprintf(6, ["L=%a has minimal elements M=%a and lcm's are C=%q", L, M, C]);
    map(`cs/II/hull`, C, M, H);  
  end:
  
   
  `cs/II/hull` := proc(u, M, ATC(H,table), $) 
    local i, h, oldh, oldM, S, G, r, cr, rr;
    uses `JetMonomTools/J`;
    G := `cs/H/node`(u, H);
    i, oldh, oldM := op(G);
    S := sets(u, M minus oldM);  rprintf(7, ["%a: oldM=%a, oldH=%a, sets(%a, %a)=(%q)", 
                                               u,      oldM,    oldh,     u, M minus oldM, S]);
    h := hull(S , op(oldh));   rprintf(6, ["%a: <%a, %a> = %q", u, S,  oldh, h]);  
    #print(OLDH, u, H[u]);
    H[u][3] := M;
    H[u][2] := h;
    #print(NEWH, u, H[u]);
    return h;
  end:
  
  `cs/II/classes` := proc(ATC(rs,set), ATC(u,Jcount), ATC(L,set), $)
    option inline;
    select(proc(s) local q; evalb(`JetMonomTools/J`:-divideNot1(u,s,q) and (`JetMonomTools/J`:-vars(q) subset rs)) end, L)  
  end:
  
  `cs/combine` := proc(ATC(L,sequential(Jcount1)), ATC(H,table), $)
    map(`cs/combine/1`, [indices(H,nolist)], L, H);
  end:
  
  `cs/combine/1` := proc(ATC(u,Jcount), ATC(L,sequential(Jcount1)), ATC(H,table), $)
    local M, i, ii, h, res, N1, N2, r, cr, rr;
    assert(assigned(H[u]));
    i, h, M := op(H[u]);
    ii := map(`cs/II/classes`, map(`minus`, h minus {{'CI'}}, {'CI'}), u, L) minus {{}}; # 'CI' is auxiliary item signalizing 1-st kind cc
    N1 := nops(i);
    N2 := nops(ii);     
    if N1 = 0 then 
      if N2 > 1 then # second kind only
        res := u = ii 
      else
        res := NULL;
      fi
    elif N1 = 1 then 
      if N2 > 1 then # already resolved first kind and second kind
        r := op(op(i) minus {u});
        #cr, rr := selectremove(curry(`subset`, {r}), ii);
        cr, rr := selectremove(proc(a) `subset`({r}, a) end, ii);
        rprintf(1, ["Looking for class containing %a in %a and joining %a to it. Found %a, remains %q",
                                                  r,    ii,            u,              cr,         rr]);
        assert([nops(cr)=1, "Inconsistent hypergraph item %q", H[u]]);        
        res := u = {op(cr) union {u}} union rr;
      else
        res := NULL;
      fi      
    else 
      if N2 = 0 then # first kind only
        res :=  u = i;
      else # (unresolved) first and second kind
        res :=  u = ii union {{u}};
      fi;
    fi;
    rprintf(5, ["cc at %a created: %a; combined from i=%a, ii=%a.", u, [res], i, ii]);    
    return res;
  end;
	
	#
	# marking cc's as fulfilled (by joining their classess in hypergraph H)
	#
  markFF := proc(ATC(u,Jcount), ATC(r,Jcount1), ATC(s,Jcount1), ATC(H,table), $)
	  description 
		  "Marks in hypergraph H the cc at u of r and sas fulfilled so no more generated.\
		   The return value is not defined.";
		# is it cc of first or second kind?
		local t, cr, cr1, rest, N, ip;
  	`cs/H/checktype`(u, H, level=1);
  	assert([`JetMonomTools/J`:-divide1f(u, r), "Wrong arguments, r=%a must divide u=%a", r, u ]);
  	assert([`JetMonomTools/J`:-divide1f(u, s), "Wrong arguments, s=%a must divide u=%a", s, u ]);
  	assert([r<>s, "Wrong arguments, r and s must differ but are equal %a", r]);
		if u=r or u=s then 
			N := nops(H[u][1]);
		  t := `if`(u=r, s, r); # choose t as the smaller of r,s (u is the bigger)			
			if   N=0 then 
			  error "No first kind cc in hypergraph at %1", u;
			elif N=1 then # SECOND kind (with resolved first kind cond. in the class - mixed)  	
        `markFF/2`(u, r, s, H);        
			elif N=2 then	# FIRST kind
			  assert([ {u} in H[u][1], "Wrong hypergraph implementation, missing {%a} in H[%a][1]=%a", u, u, H[u][1]]);  
			  assert([ member(t, op(H[u][1] minus {{u}})), 
			           "Monomial %a is not member of first kind cc classess at %a, H[%a][1]=%a", t, u, u, H[u][1]]);			  			  
			  H[u][1] := {{r,s}};			  
			  #cr, rest := selectremove(curry(`subset`, `JetMonomTools/J`:-vars(u/t)), H[u][2]);
			  cr, rest := selectremove(proc(a) `subset`(`JetMonomTools/J`:-vars(u/t), a) end, H[u][2]);
			  assert(nops(cr)<=1);
			  if cr = {} then cr1 := `JetMonomTools/J`:-vars(u/t) else cr1 := op(cr) fi;
		    H[u][2] := map(p -> if p={'CI'} then ip:= true; {'CI', op(cr1)} else p fi, H[u][2]);			 
			  if ip=true then # first kind only
			    rprintf(7, ["joined %a and %a, H[%a][1]=%q", r, s, u, H[u][1]]);
			    H[u][1];
			  else # mixed     
          rprintf(7, ["(1) at H[%a][2]=%a, joining %a=%a: found class %a, remains %q", 
                                u,     H[u][2],    r, s,              cr,         rest]);
          assert(nops(cr)=1);
          H[u][2] := (rest minus {{'CI'}}) union {op(cr) union {'CI'}};
        fi;
			else
			  error "Hypergraph implementation error, too much first kind classess, H[%1]=%2", u, H[u]; 
			fi;
		else # SECOND kind
      `markFF/2`(u, r, s, H);
		fi;
	end:
	
	`markFF/2` := proc(ATC(u,Jcount), ATC(r,Jcount1), ATC(s,Jcount1), ATC(H,table), $)
  	local cr, cs, rest;
    # find classes whose r and s are representatives 
    if u/r <> 1 then
      #cr, rest := selectremove(curry(`subset`, `JetMonomTools/J`:-vars(u/r)), H[u][2]);
      cr, rest := selectremove(proc(a) `subset`(`JetMonomTools/J`:-vars(u/r), a) end, H[u][2]);
    else
      #cr, rest := selectremove(curry(member, 'CI'), H[u][2]);
      cr, rest := selectremove(`member/CI`, H[u][2]);
    fi;
    if u/s <> 1 then 
      #cs, rest := selectremove(curry(`subset`, `JetMonomTools/J`:-vars(u/s)), rest);
      cs, rest := selectremove(proc(a) `subset`(`JetMonomTools/J`:-vars(u/s), a) end, rest);
    else
      #cs, rest := selectremove(curry(member, 'CI'), rest);  
      cs, rest := selectremove(`member/CI`, rest);   
    fi;
    rprintf(7, ["(2) at H[%a,2][2]=%a, joining %a=%a: found classess %a and %a, remains %q", 
                u,  H[u][2], r, s, cr, cs, rest]);
    assert([nops(cr)=1 and nops(cs)=1, 
            "Implementation error, u=%a, r=%a, s=%a, H[u]=%a, cr=%a, cs=%a, rest=%a", u, r, s, H[u], cr, cs, rest]);
    # join the classes found and put the result back to H
    H[u][2] := rest union {op(cr) union op(cs)};	
	end:
	
  #
  # assembling cc's from generating classess
  #
  cc := proc(Ls::uneval, # {unknown={Jcount1, ...}, ...}
             Hs::table:=HS, # Hs is table of hypergraph tables
              {##  keywords for selection of a "portion" of cc's returned:
                 maxnum::{posint,identical(-1)} := -1, # total maximum number of returned cc's
                 maxnumP::{posint,identical(-1)} := -1, # return maxnumP items and add all cc's of same prices as last item
                 maxprice::{numeric,infinity} := infinity, # maximal price of cc's to be returned
                 # in all above parameters, -1 means no limitation
						   ## marking:
						     pop::truefalse:=false, # mark the returned portion as fullfilled
						   ## pricing funstions:
                 sidePriceFunction := stupidSidePrice,
                 combinePriceFunction := `combinePrices/+`,
							 ## aditional return information
							   totalNumber::symbol:='None' # total number of actual cc's
						   }, $) 
     description 
		   "Returns a portion (limited by selection keywords preffering the cheapest one's)\
        of still not fulfilled cc's (sorted by its prices)\
        If 'pop' keyword given, marks the portion returned as fulfilled.";
     # at least 1 cc (if exists) is ALWAYS returned regardless of any selecting criteria
     # [] is returned ONLY if NO cc of any price at all exists 
     # the total number of actually existing cc's (regardless of selection) may be returned via 'totalNumber' keyword
		 # the order of returned cc's of the same prices is not defined
     # default values of selecting criteria may change in future versions
	   local LT, Us, prcs, selprcs, ccs, p, N;
	   # parse the first argument to table format and do some type checks
	   if type(Ls, table) then
	     Us := [indices(Ls, nolist)];
	     assert(andmap(U -> if type(Ls[U], sequential(Jcount1)) then true 
                          else
                             error "Wrong first argument: there is entry Ls[%1]=%2 of wrong type in the table Ls.", U, Ls[U]
                          fi, eval(Us,1)));
	     LT := Ls;
	   elif type(eval(Ls, 2), equation) then
	     assert([type(Ls, anything=sequential(Jcount1)), "Wrong first argument %a format", Ls]);
	     LT := table([eval(Ls,2)]);
	     Us := [lhs(eval(Ls,2))];
	   elif type(eval(Ls, 2), sequential) then
	     assert([type(Ls, sequential(anything=sequential(Jcount1))), "Wrong first argument %a format", Ls]);
	     LT := table(eval(Ls,2));
	     Us := [indices(LT, nolist)];
     else
 	     error "Wrong first argument Ls=%1, "\
 	           "it must be of the form {unknown={Jcount1, ...}, ...} "\
 	           "or table([unknown={Jcount1, ...}, ...])", eval(Ls,2);
 	   fi;
 	   # check whether input is of correct jet implemantatio J[...], i.e. NOT of the jet(...) format 
 	   assert([not(has(LT, jet)), "Implementation error, jet variables must be in J[] format!"], level=3);
 	   # check the second argument (table of hypergraph tables)
     assert([type(Hs, table), "Wrong argument: H must be table."], level=0);
     # add missing empty hypergraphs to Hs
     map(U -> if not assigned(Hs[evaln(U)]) then Hs[evaln(U)] := table(); fi,  Us);
     ### find sufficient cc's - get the complete list of cc's (prices attributed by the cc's)
     rprintf(3, ["Lets find cc's of %q", op(map(U -> ''U''=LT[U], Us))]);
     prcs := map(U -> `cc/attr/priced`(LT[U], evaln(U), eval(Hs), 
                                       ':-sidePriceFunction'=sidePriceFunction, 
                                       ':-combinePriceFunction'=combinePriceFunction),
                       Us);
     ### select a portion of cc's to be returned (specified by keyword parameters)
     N := nops(prcs);
		 totalNumber := N;
     rprintf(3, ["Found totally %a cc's of %q, lets do some selection.", N, op(map(U -> ''U''=LT[U], Us))]); 
     selprcs := prcs;
     if   N=0 then return [] 
     # elif N=1 then nothing to select, take this single cc
     elif N>1 then 
       # do the selection
       if maxprice <> infinity then 
         selprcs := select(`<=`, selprcs, maxprice);
       fi;
       if maxnumP <> -1 then 
           p := setattribute(selprcs[maxnumP]);
           selprcs := select(`<=`, prcs, p) 
       fi;
       if maxnum <> -1 and nops(selprcs) > 1 and nops(selprcs) > maxnum then
         selprcs :=  selprcs[1..maxnum];
       fi;
     fi;
     # return at least 1 cc regardless of filtering criteria
     if nops(selprcs) = 0 then selprcs := [prcs[1]] fi; 
     # forget the prices and take the cc's instead
	   ccs := map(attributes, selprcs);	 
	   # mark selected cc's as fullfilled
	   if pop then map(c -> markFF(c[2], lhs(c[3]), rhs(c[3]), eval(Hs['c'[1]])), ccs) fi;
	   # return selected cc's
     rprintf(1, ["Returning %a (of totally %a) cc's of %q. ", nops(ccs), N, op(map(U -> ''U'', Us))]); 
	   rprintf(2, ["cc()=%q\n",ccs]);
	   return ccs;
	 end:
	 
	 `cc/attr/priced` := proc(ATC(L,sequential(Jcount1)), U:='NotSpec', ATC(Hs,{table, identical(NULL)}):=NULL, 
              {sidePriceFunction:= stupidSidePrice,
						   combinePriceFunction:= `combinePrices/+`}, $)
	   local ccs, prcs;
 	   rprintf(4, ["Computing cc(%q)...", args]);
	   ccs := convert(classess(L, `if`(Hs=NULL, NULL, Hs[U])), list);
	   prcs := map(`cc/1/attr/ass`, ccs, U, _options);
	   rprintf(3, ["cc(%a,%a)=%a", L, U, map(r -> attributes(r)=r, prcs)]);
	   return op(prcs);
	 end:

	 
	#
	# assembling cc's of given unknown U at given point p from generating classess stored in H[U][p]
	#
	`cc/1/attr/ass` := proc(ATC(c,`CC/class`), U:='NotSpec', 
													{sidePriceFunction:= stupidSidePrice,
													 combinePriceFunction:= `combinePrices/+`},$)
		description 
		"Assembles all cc's at given point.\
		H[p] is the set of cc classess of the unknown U at given point p.\
		This function chooses representatives of each class, assembles the all cc's and\
		returns the sequence of prices attributed by assembled cc's of the form\
		[U, p, i, j]";
		
		local p, rs, ars, r;
		p := lhs(c);
		rs := rhs(`cc/repr/chooser/1/attr/rhs`(c, U, sidePriceFunction));
		# prices are known, assemble cc's
		if nops(rs)=0 then
			error "empty cc class of %1 at %2", U, p; 
		elif nops(rs)=1 then
		  NULL # single class means no cc (or cc's already fulfilled)
		else
		  # assemble all cc's by rule fist <-> second, ..., fist <-> last
			r := rs[1]; 
			ars := map(s->setattribute(combinePriceFunction(U, p, r, s), attributes(r) = attributes(s)), 
			           rs[2..-1]); 
      # return sequence of prices attributed by cc records of the form [U, p, i, j]
			op(map(a -> setattribute(a, [U, p, attributes(a)]), 
			       ars))			
		fi;
  end;
	
	`combinePrices/+` := proc(U, p, ATC(r,numeric), ATC(s,numeric), $)::numeric; 
		description 
			"Given two prices r, s (attributed by sides of cc to be assembled, for unknown U at point p),\
			returns the cost of that cc";  
			option inline;
			r+s;
  end:	
	# TODO: Smart combine functions may be useful
	
  `cc/repr/chooser/1/attr/rhs` := proc(ATC(c,`CC/class`), U, F, $)
    description 
      "Given single cc of the form p={{class1}, {class2}} and pricing function F,\
       computes the computational price of each representative,\
       chooses the minimal cost representative of each class\
       and returns p = [price1, price2, ...] \
       representatives attached as Maple attributes to each price";
    local ccs, res, F1;
    ccs := map(convert, rhs(c), list); # the clasess as lists
    F1 := proc(a) F(U, lhs(c), a) end;  
    #F2 := curry(F, U, lhs(c));
    #print(aa,F1);
    #print(bb,F2);
    assert([andmap(`>`, map(nops, ccs), 0), "Empty item in cc class %q", map(attributes, ccs)]);
    res := map(min@op@attLBySize, ccs, F1); 
    res := sort(convert(res,list), `<`);
    rprintf(9, ["Prices are %a.", map(p->p=map(F1, p), ccs)]);                      
    rprintf(5, ["Representatives at %a of %a are\n %a.", lhs(c), ccs, map(r->attributes(r)=r, res)]);                      
    return lhs(c) = res;                  
  end:  

  
  stupidSidePrice:= proc(U, p, m)::numeric;
    description 
      "General procedure for computing computational cost of evaluating of ONE SIDE of cc.\
      This general version is extremely noneffecctive,\
      since does not use any information about the unknown in question nor its derivatives.\
      Please give an appropriate specific cost function as argument to the assembling routines.";   
   local q;
   DOE(`stupidSidePrice/PrintWarning`());
   
   if `JetMonomTools/J`:-divide1(p,m,q) then degree(q) else error "Cannot compute price at %1: %2 |/ %3 ", U, p, m; fi; 
  end:
  
  `stupidSidePrice/PrintWarning` := proc() 
    option remember; # print this warning only once
    WARNING("Using of the primitive general cost function is strongly noneffective.");
  end:
  
  `member/CI` :=  proc(a) member('CI', a) end: # curry(member, 'CI')
  
  
  # auxiliary logging
  
  rprintf := proc(level, msg_list::{uneval,list}) 
    convert(procname,'`global`')(args, ':-levelName'='CC')
  end:

  rlprint := proc(level, msg_list::{uneval,list})
    convert(procname,'`global`')(args, ':-levelName'='CC')
  end:
    
    
end module:


###################################################################################################
# General auxiliary utilities
###################################################################################################

#
# assertions
#

AssertLevel := proc(n::integer)
  description "Sets (the global) assertion level.";
  global assert, `assertlevel/value`;
  kernelopts('assertlevel'= max( min(n, 2),  kernelopts('assertlevel')));
  `assertlevel/value` := n;
  if n > -infinity then
    assert := proc(c::uneval, {level::integer:=1, callstackskip::posint:=0})
      description 
        "Checks whether the given assertion condition is true.\
         This test is run only if the given level is bellow the global assert level\
         otherwise no evaluation is proceeded and nothing is tested.\
         Argument c may be the condition itself or a list of the form \
         c=[condition, message_format_string, message_opt_argument, ...]\
         (the message is then created by calling sprintf(message_format_string, message_opt_argument, ...))";
      global `assertlevel/value`;
      local evc, s, message;
      if level=0 or (assigned(`assertlevel/value`) and evalb(level <= `assertlevel/value`)) then 
        if type(c, list) then
          evc := eval(c[1]);
        else
          evc := eval(c);
        fi;     
        if evalb(evc) <> true then
          s := debugopts('callstack')[5+3*callstackskip];
          if type(c, list) and nops(c)>=2 then
            message := sprintf(op(eval(c[2..-1])));
            error "Assertion failed (in %1): %2", s, message;			  
          else
            printf("assert(unevalued): %q\n", c);
            printf("assert(evalued):   %q\n", evc);
            error "Assertion failed (in %1): %2, %3", s, c, evc; 
          fi;    
        else
          if type(evc, equation) then lhs(evc) else evc fi;
        fi;
      else
        "Assertion ignored"
      fi;
    end:
    "Assertions level", n
  else
    assert := proc(c::uneval) "Assertions disabled" end:
    "Assertions disabled"
  fi;
end:

$ifdef jets_mode_debugging
  AssertLevel(0):
$else
  assert := proc(c::uneval) "Assertions disabled" end:
$endif

#
# logging and messaging
#

LogLevel := proc(n::{integer,identical(NULL)}:=NULL, Ls::seq(name=integer):=NULL)
  description 
   "Sets the log level(s).\
    loglevel(n) sets the global (default) log level to n\
    loglevel(m1=n1, ...) sets the 'm1'-named level to n1 etc";
  global `loglevel/value`,  `assertlevel/value`;
  if nops([n, Ls]) > 0 then 
    if not(assigned( `assertlevel/value`)) then  `assertlevel/value` := n fi; # set the assert level too
    if not(assigned(`loglevel/value`)) then `loglevel/value` := table() fi; # create empty level table if none exists
    if n <> NULL then `loglevel/value`[`global`] := n; fi; # assign global level
    map(m -> assign('`loglevel/value`[lhs(m)]', rhs(m)), [Ls]);  # assign local levels
  fi;
  if assigned(`loglevel/value`) then op(op(op(1,`loglevel/value`))); else NULL fi; # return actual settings
end:

`loglevel/test` := proc(levelValue, levelName:=`global`)
  global `loglevel/value`;
  if not(assigned(`loglevel/value`)) then
    false
  else 
    if assigned(`loglevel/value`[levelName]) then
      evalb(levelValue <= `loglevel/value`[levelName])
    else
       assigned(`loglevel/value`['`global`']) and evalb(levelValue <= `loglevel/value`['`global`'])  
    fi;
  fi;
end:

sprintCallingFunction := proc(n::posint)
  description "sprints the name of calling function enquoted by as much spaces as call stack size plus n";
  local CS, s, m, u, q; 
  CS := debugopts('callstack');
  q := sprintf(cat(" " $ (nops(CS)-1-3*(n+2))/3*2));
  u := "";
  for m from 0 to (nops(CS)-1)/3 by 1
    while   s='s'
            or convert(s,string)=convert(procname, string)
            or convert(s,string)="rprintf"
            or convert(s,string)="rlprint"
            or convert(s,string)[1..8]="unknown/" 
    do 
      s := CS[2+3*m] ; 
      if convert(s,string)[1..8]="unknown/" then u := cat(u, "*") fi;
  od;
  sprintf("%s%s%s: " , q, s, u);  
end:

rprintf := proc(level, msg_list::{uneval,list}, {levelName:=`global`}) 
 global `loglevel/value`; # TODO: replace by report level
 local cfs, msgle,qs, fs;
 if `loglevel/test`(level, levelName) then
   # enquote string for the first line 
   cfs := sprintCallingFunction(2); 
   # enquote string for the remaining lines
   qs := cat("\n",  StringTools[Fill](" ", length(cfs)-2), ": ");
   msgle := op(eval(msg_list));
   # enqoute \n's by appropriate spaces (except the last \n) in formatting string
   fs := StringTools[RegSubs]("((\n[^$]))"=qs, msgle[1]); 
   printf("%s", cfs); # first line quotation
   printf(fs, msgle[2..-1]); # message
   printf("\n");
 end:
end:

rlprint := proc(level, msg_list::{uneval,list}, {levelName:=`global`})
 global `loglevel/value`; # TODO: replace by report level
 if `loglevel/test`(level, levelName) then
   lprint(sprintCallingFunction(2));
   lprint(op(eval(msg_list)))
 end:
end:

################################################################################
################################################################################
# Transactional i/o routines 
################################################################################
################################################################################


module TransactionIOTools()
  export    
    removeFile, waitForFile, waitForRename, readFile;

  removeFile := proc(f, {warning:=false})
    if FileTools[Exists](f) then
      if warning and FileTools[Size](f) > 0 then 
         WARNING("Removing file %1", f); 
      fi;
      FileTools[Remove](f);
    fi;  
  end:

  waitForFile := proc (f)
    while not(FileTools[Exists](f)) do WARNING("waiting for file %1", f); ssystem("sleep 1") od;  # TODO(sysdep)
  end:
  
  
  waitForRename := proc(source, target, {maxAttemptsLimit:=5, afterLimit::identical(FAIL,ignore):=FAIL})
    local d;
    d := 0;
    while d<maxAttemptsLimit do
      try
        FileTools:-Rename(source,target);
        return true;
      catch "source file does not exist":
        if d=0 then WARNING("waiting for file %1", source);fi;
        d := d+1;
        ssystem("sleep 1") # TODO(sysdep)
      end:
    od;
    if afterLimit=FAIL then 
      FileTools:-Rename(source,target);
      return true;
    else
      return FAIL;
    fi;
  end:

  
  readFile := proc(file::string, {skipEmptyLines::truefalse:=false})::list(string);
    description "Returns a list of lines of a given file, each line as a string";
    local s, r;
    s := FileTools[Text][ReadFile](file);
    if s<>0 then
      r := StringTools[Split](s, "\n");
      if skipEmptyLines then 
        return remove(l -> length(l)=0, r);
      else
        return r;
      fi; 
    else
      []
    fi;
  end:

end module:

TransactionWriter := proc(  BaseDirPath::string  := ".",  
                            MainFileName::string := 
                                  cat(op(2,ssystem("echo $HOSTNAME")) , `.`, kernelopts(pid)), # TODO(sysdep)
                            {suppressCleanUp::truefalse := false,
                             mode::name:='none',
                             locking::identical(none,wait):='none'
                             }, $)
  description "Returns an initialized instance of transactional writer module.";
  module ()
    export 
      baseDirPath,
      mainFileName, mainFile, 
      ModulePrint,
      ModuleApply,
      AppendLine;
    local
      Init,
      newFile, oldFile;
    uses TransactionIOTools;
    
    Init := proc ()
      local fd;
      # setup the directories and filenames
      mainFileName := MainFileName;
      baseDirPath  := `if`(BaseDirPath[-1]="/", BaseDirPath, cat(BaseDirPath, "/")); # TODO(sysdep)  
      print(baseDirPath);
      FileTools[MakeDirectory](baseDirPath, recurse=true);
      mainFile := FileTools[AbsolutePath](mainFileName, baseDirPath);
      oldFile  := FileTools[AbsolutePath](cat(mainFileName, ".bak"), baseDirPath);
      newFile  := FileTools[AbsolutePath](cat(mainFileName, ".tmp"), baseDirPath);
      # cleanup old files 
      removeFile(oldFile, warning);
      removeFile(newFile, warning);
      if not suppressCleanUp then 
        if FileTools[Exists](mainFile) then
          if FileTools[Size](mainFile) > 0 then
             WARNING("File %1 already exists, moving to %2", mainFile, oldFile);
          fi;
          FileTools[Rename](mainFile, oldFile);
        fi;
      fi;
      # setup the mode, i. e. the default write function and its behavior
      if mode = append then 
        ModuleApply := AppendLine;
        # touch the main file    
        fd := FileTools[Text][Open](mainFile, create=true, overwrite=true);
        FileTools[Text][WriteString](fd,""); 
        FileTools[Text][Close](fd);     
      elif mode = none then
        ModuleApply := proc() error "Default mode not set, use the explicit call." end
      else
        error ("unknown mode %1", mode);
      fi;
    end:
    
    ModulePrint := proc()
      print("writer:", mode, locking, baseDirPath, mainFileName, mainFile, newFile, oldFile);  
    end:
    
    AppendLine := proc()
      local fd;    
      # grab the file      
      removeFile(newFile, warning);
      if locking=wait then
        waitForRename(mainFile, newFile);
      else
        FileTools[Rename](mainFile, newFile);
      fi;     
      removeFile(oldFile);    
      FileTools[Copy](newFile, oldFile);
      # do the output
      fd := FileTools[Text][Open](newFile, append=true);
      map2(FileTools[Text][WriteLine], fd, map(convert, [args], string));
      FileTools[Text][Close](fd);
      # put the file on his place
      FileTools[Rename](newFile,  mainFile);
    end:
    
    Init(); # init the module    
  end module;
end:

TransactionReader := proc(  BaseDirPath::string,  
                            MainFileName::string,
                            {locking::identical(none,wait):='none',
                             skipOld::truefalse:=false, # skipping lines already readed (i.e. never return one line twice)
                             skipEmptyLines::truefalse:=false
                             }, $)
  description "Returns an initialized instance of transactional reader module.";
  module ()
    export 
      baseDirPath,
      mainFileName, mainFile, 
      ModulePrint,
      ModuleApply,
      ReadFile;
    local
      Init,
      tempFile, actualLine;
    uses TransactionIOTools;
    
    Init := proc ()
      local fd;
      # setup the directories and filenames
      mainFileName := MainFileName;
      baseDirPath  := `if`(BaseDirPath[-1]="/", BaseDirPath, cat(BaseDirPath, "/")); # TODO(sysdep)  
      FileTools[MakeDirectory](baseDirPath, recurse=true);
      mainFile := FileTools[AbsolutePath](mainFileName, baseDirPath);
      tempFile  := FileTools[AbsolutePath](cat(mainFileName, ".locked"), baseDirPath);
      if skipOld then actualLine := 0 fi;
    end:
    
    ModulePrint := proc()
      print("reader:", locking, skip, baseDirPath, mainFileName, mainFile, tempFile);  
    end:
    
    ModuleApply := ReadFile;
    
    ReadFile := proc()
      local s, n, N;
      # read the whole main file
      if locking=wait then
        if waitForRename(mainFile, tempFile, afterLimit=ignore) = FAIL then
          WARNING("Reading of unaccessible file %1 skipped", mainFile);
          return;
        fi;
        s := readFile(tempFile, ':-skipEmptyLines'=skipEmptyLines);
        FileTools[Rename](tempFile, mainFile);        
      else
        s := readFile(mainFile, ':-skipEmptyLines'=skipEmptyLines);
      fi;
      if not skipOld then
        # return whole file
        return s
      else
        # return just the new lines
        n := nops(s);
        if   n < actualLine then error "Missing lines in %1", mainFile 
        elif n = actualLine then return []
        else N := actualLine; actualLine := n; return s[N+1..n]
        fi
      fi;
    end:
    
    Init(); # init the module    
  end module;  
end:  

################################################################################
################################################################################
# Multiordering CC routines (optional code)
################################################################################
################################################################################

# Routines to run a single computation in several instancies, each of them:
# * Uses different variable ordering
# * Exports obtained compatibility conditions
# * Imports c.c. exported by others (and uses them)
#
# Such a sharing of c. c. is done on the fly within `run/l`() procedure.
#
# Implementation of the sharing is based on shared files, 
# one file of exported cc per instance (names must not conflict)
# plus one global file with list of instancies.
# All the files resides in a common direcory 
# and the computations may bu run on any computer(s) which has r/w access to this directory.
#
# Usage:
#   `Jets/opts`["Optionals"]["Multiord"]) := true; # enable the optional source code
#   read("Jets.s");
#   MultiOrdCC("myExportFile.s", "WorkingDirectory"); # initialize
# Caution: myExportFile.s must be UNIQUE for each instance


if not(assigned(`Jets/opts`["Optionals"]["Multiord"])) then
  module MultiOrdCC()
    export Pop, Write, Init;
    Write := proc() end:
    Pop   := proc() end:
    Init  := proc() error "Feature disabled." end: 
  end:
else
  module MultiOrdCC()
    export Pop, Write, Init,
      RefreshReaders,
      ModulePrint,
      ModuleApply;
    local
      mCCDir, mCCProducersListFile,
      writer,
      readers;
    uses TransactionIOTools;
    
    writer := proc() error "Module not initialized" end: 
    Write := proc() end:
    readers := {}:
    
    Init := proc(id::string:=NULL, dir:="CCData/")
      local fd; 
      mCCDir := dir;
      mCCProducersListFile := cat(mCCDir, "Producers.txt"):
      # create tranasctional writer
      writer := TransactionWriter(mCCDir, id, mode=append, locking=wait);
      # register the output to the global list of producers
      if FileTools[Exists](mCCProducersListFile) 
         and (has(readFile(mCCProducersListFile), writer:-mainFileName)) then
        WARNING("The file %1 is already registered in %2.", writer:-mainFile, mCCProducersListFile);
      else 
        fd := FileTools[Text][Open](mCCProducersListFile, append=true, create=true);
        FileTools[Text][WriteLine](fd, writer:-mainFileName);
        FileTools[Text][Close](fd);
      fi;
      # printf("CC will output intermediate progress to %a\n", ccTW:-mainFile);
      Write := writer;
      writer:-mainFile;
    end:
    
    ModuleApply := Init;
    
    ModulePrint := proc()
      print(mCCDir, mCCProducersListFile);
      print(writer);
      map(print, readers);
    end:
  
    RefreshReaders := proc()
      local regs, aux, fs;
      # read the file with registrations
      regs := convert(readFile(mCCProducersListFile, skipEmptyLines), set);
      # remove unregistered readers
      readers, aux := selectremove(r -> r:-mainFileName in regs , readers);
      if nops(aux) > 0 then printf("Removing unregistered readers %q\n", aux) fi;
      # add new readers
      fs := map(r -> r:-mainFileName, readers);
      aux := remove(r -> r in fs, regs) minus {writer:-mainFileName};
      if nops(aux)>0 then
        printf("Adding new readers %q\n", aux);
        readers := readers 
          union map(r -> TransactionReader(mCCDir, r, locking=wait, skipOld, skipEmptyLines), aux);
      fi;
      map(r -> r:-mainFileName, readers);
    end:
    
    Pop := proc()
      RefreshReaders();
      map(parse, map(r -> op(r:-ReadFile()), readers))
    end:
  end module:
fi:


################################################################################
################################################################################
# Data report ouput routines 
################################################################################
################################################################################

# Reporter() returns a configured callable module.
# On its invocation the parameters are writen to the disc (in the way specified when output module was created)
CreateDataReporter := proc(baseFileName::string, {ext::string:=".log", dir::string:=".",
           mode::{identical(append, Append, rewrite, incremental,Incremental)}:=append,
           incProc::procedure:=NULL,
           suppressComments::truefalse:=false, incDelim::string:="_",
           outputProc := sprintf,
           addOutArgs := NULL})
           ### mode - single output file modes:
           # append - at startup, clears the output file; all the output is appended
           # Append - all the output is appended (even to already existing file)
           # rewrite - output file is cleared before every output
           ### mode - multiple output file modes:
           # icremental - there is created a new file on every index value (by default, indexes 1, 2, ... are appended to the file name)
           # Incremental - ditto, but output is appended if (indexed) file already exists
  module()
    export ModuleApply;
    local Init,
          N, M, myIncProc,
          mainFilePath, backupFilePath;
    
    Init := proc()
      N := 0;
      myIncProc := `if`(incProc=NULL, proc() N := N + 1; end, incProc);
      FileTools[MakeDirectory](dir, recurse=true);
      if mode='incremental' or mode='Incremental' then  
        mainFilePath := proc(i) FileTools[AbsolutePath](cat(baseFileName, incDelim, i, ext), dir) end:
        backupFilePath := proc(i) FileTools[AbsolutePath](cat(baseFileName, incDelim, i, ext, ".bak"), dir) end:        
     else 
        mainFilePath := proc(i) FileTools[AbsolutePath](cat(baseFileName, ext), dir) end:
        backupFilePath := proc(i) FileTools[AbsolutePath](cat(baseFileName, ext, ".bak"), dir) end:   
        TransactionIOTools:-removeFile(backupFilePath());  
        if FileTools:-Exists(mainFilePath(i)) then 
          if mode='Append' then FileTools:-Copy(mainFilePath(i),backupFilePath(i))
          else FileTools:-Rename(mainFilePath(i),backupFilePath(i)) fi;
        fi;    
      fi;
    end:
    
    Init();
    
    ModuleApply := proc({comment::{string}:=""})
      local fd, bf, nf, i;
      i := myIncProc(); 
      nf, bf := mainFilePath(i), backupFilePath(i);
      if i <> M then
        # backup and cleanup
        TransactionIOTools:-removeFile(bf);
        if FileTools:-Exists(nf) then
          if mode='incremental' or mode='rewrite' or (type(mode, indexed) and i <> M) then 
               FileTools:-Rename(nf,bf) 
          else FileTools:-Copy(nf,bf)  
          fi;
        fi;
      fi;
      # the output
      fd := FileTools[Text][Open](nf, create=true, append=true);
      if not(suppressComments) then 
        FileTools[Text][WriteString](fd, 
          cat( `if`(i=M,"", "#################\n"),
               sprintf("### STEP %q ###\n", i), 
               `if`(comment="", "", sprintf("# %s\n", comment)))); 
      fi;
      FileTools[Text][WriteString](fd,outputProc(args, addOutArgs)); 
      FileTools[Text][Close](fd);  
      M := i;
    end:       
  end:
  
end:

DoReports := proc(a::evaln, es)
  global reporters;
  local ops := _passed[3..-1];
  map(r -> r(es,ops) , reporters[a]);
end:


################################################################################
################################################################################
# General utilities
################################################################################
################################################################################

`index/traceless` := proc( idx :: list( posint ), M::Matrix, val::list ) 
  description "Index function of traceless matrices";
  local i, j, init_val, N;
         if nops(idx) <> 2 then
             error "Matrix indexing requires exactly 2 indices";
         end if;
         i, j :=  op(idx);
         N := op(2,rtable_dims(M)[1]);
         if nargs = 2 then
             # retrieval
                 if i=j and i=N then
                 -add(M[k,k], k=1..N-1)                 
             else
                 # get value from storage
                 M[i,j];
             end if;
         else
             # storage
             if  i=j and i=N then
                 # indexing function determines value, i.e.,
                 # location is not mutable
                 if op( val ) <> -add(M[k,k], k=1..N-1) then
                     # invalid value
                     error "invalid assignment";
                 else
                     # be sure to do explicit write, but catch
                     # this if the storage fails, as storage
                     # for non-mutable locations need not be
                     # allocated
                     try
                         M[i,j] := op( val );
                     catch "unable to store":
                         # couldn't write, return value (as if
                         # the write succeeded)
                         op( val );
                     end try;
                 end if;
             else
                 # general value
                 M[i,j] := op( val );
             end if;
         end if;
     end proc:
     
################################################################################
################################################################################
# JetMachine Module
################################################################################
################################################################################     
     
     
module JetMachine () 
  export Consequences; # Consequences (aka special cases) test suite

  ##############################################################################
  # Consequences (aka special cases aka maximal results) test suite
  ##############################################################################

  module Consequences()
    export AmICons, ListGen, TestGen, ExportGen;
    local `AmICons/put`, `AmICons/dependence`, `AmICons/nonzero`;
   
    AmICons := proc(fileName)
      description "test whether the current jets environment is the consequence (a special case)"
                  " of the environment stored in the file specifyed";
      local f, s, e, n, r, t;
      
      # read in the source file
      f := FileTools[Text][Open](fileName, create=false, overwrite=false);
      try
        s := FileTools[Text][ReadFile](f);
      finally
        FileTools[Text][Close](f);
      end;
    
      # the procedures bellow must NOT be called directly, we have to tweak it in order to catch the the calls
      s := StringTools:-SubstituteAll(s, "put", "JetMachine[Consequences]:-`AmICons/put`");
      s := StringTools:-SubstituteAll(s, "dependence", "JetMachine[Consequences]:-`AmICons/dependence`");
      s := StringTools:-SubstituteAll(s, "nonzero", "JetMachine[Consequences]:-`AmICons/nonzero`");
  
      # parse tweaked version of source file
      n := 0;
      while n<StringTools[Length](s) do
        try
          r := parse(s, 'lastread'='n','offset'=n,statement);
        catch "numeric exception: division by zero":
          printf("Division by zero => false\n");
          return false
        end;
        if eval(r)=false then 
           return false 
        fi;
      od; 
      return true;
    end;
  
    `AmICons/put` := proc() 
      andmap(proc(a) 
               local e;
               e := simpl(lhs(a)-rhs(a)); 
               if evalb(e=0) then return true else printf("%a <> %a\n", lhs(a), rhs(a)); return false; fi;
             end, 
             [args])
    end;
    
    `AmICons/dependence` := proc() 
      local d1, d2;
      d1 := map(lhs, {dependence()});
      d2 := map(lhs, {args});
      if not(d1 subset d2)  then # do we have all unknowns?
        printf("Missing dependencies: %a is not subset of %a\n", d1, d2);
      else # does dependences match?
        andmap(proc(a) 
                 local v ;
                 v := vars(lhs(a));
                 if (v subset rhs(a)) then return true;
                 else printf("Dependences of %a(%a) is not a subset of %a\n", lhs(a), v, rhs(a)); 
                   return false;
                 fi;
                end, 
               [args]) ;
      fi
    end;
    
    `AmICons/nonzero` := proc() 
      true; # just ignore nonzero() calls
    end;
      
    
   
    TestGen := proc(me::string, ignoreListFile::string:="", baseDir::string:=".", filePattern::string:="")
      description "Decides whether the exists a state OF WHICH the current environment is a consequence";
      local succ, aux, stat, res, f;
      global ignoreList;
    
      succ := FileTools[ListDirectory](cat(baseDir, "/Results/"), returnonly=cat(filePattern, "*.success"));
      aux := map(f -> f[1..-StringTools[Length](".success")-1], succ); # remove .success extension
      aux := remove(f->f=me, aux); # remove me from the list
      if ignoreListFile <> "" then
        if not(FileTools[Exists] (ignoreListFile)) then
           ignoreList := table();
        else
          read(ignoreListFile);
          if assigned(ignoreList[me]) then 
            printf("%s - Already tested and ignored (consequence of %q)\n", me, ignoreList[me]);
            return ignoreList[me] 
          fi;
          aux := convert(aux,set) minus {indices(ignoreList, nolist)} # remove ignored (non-maximal) elements
        fi
      fi;
      printf("%s - We have %a files to be tested.\n", me, nops(aux));
      # create list of pairs [basename, .state file]  to be tested
      stat := map(f -> [f, FileTools[AbsolutePath](cat(f, ".state"), cat(baseDir,"/States/"))], aux); 
      # find the generalization of me
      for f in stat do 
        printf("%s : ", f[1]);
        if  AmICons(f[2]) then 
          printf("TRUE\n"); 
          if ignoreListFile <> "" then
            ignoreList[me] := f[1];
            save ignoreList, ignoreListFile;
          fi;
          return(f[1]);  # return the generalisation found
        fi;
      od;
      return false;
    end:
    
    ListGen := proc(me::string, baseDir::string:=".", filePattern::string:="")
      description "Gives a complete list of states OF WHICH the current environment is a consequence";
      local succ, aux, stat, res;
    
      succ := FileTools[ListDirectory](cat(baseDir, "/Results/"), returnonly=cat(filePattern, "*.success"));
      aux := map(f -> f[1..-StringTools[Length](".success")-1], succ); # remove .success extension
      aux := remove(f->f=me, aux); # remove me from the list
      printf("%s - We have %a files to be tested.\n", me, nops(aux));
      # create list of pairs [basename, .state file]  to be tested
      stat := map(f -> [f, FileTools[AbsolutePath](cat(f, ".state"), cat(baseDir,"/States/"))], aux); 
      # select the generalizations of me
      res := select(proc(f)
           local r;
           printf("%s : ", f[1]);
           r := AmICons(f[2]);
           if r then printf("TRUE\n") fi;
          return r;
          end, stat);
      # return basenames only
      map2(op, 1, res);
    end:
    
    
    ExportGen := proc(exportFile::string, me::string, baseDir::string:=".", filePattern::string:="")
      description "Exports a complete list of states OF WHICH the current environment is a consequence";    
      local f, r;
      f := FileTools[Text][Open](exportFile, create=true, append=true);      
      try
        r := ListGen(me, baseDir, filePattern);
        FileTools[Text][WriteLine](f, sprintf("Generalizations[%a]:=%a;", me, r));
      finally
        FileTools[Text][Close](f);
      end;
      return r;
    end;
    
    # Note: Use the bash script bellow to test against all .Success files in a given directory:
    # #!/bin/bash
    # 
    # function MakeDir()
    # {
    #   if [ ! -d "${1}" ] ; then
    #     mkdir "${1}"
    #   fi
    # }
    # 
    # MakeDir "Consequences"
    # pushd "Consequences"
    # 
    # 
    # MyGlobalDir=".."
    # myfilebase="consequeces_`date +"%d.%m.%y_%H.%M"`"
    # zipfile="${myfilebase}.zip"
    # logfile="${myfilebase}.log"
    # 
    # echo "Zipping to `pwd`$zipfile"
    # 
    # n=0
    # m=0
    # 
    # for ko in `ls ${MyGlobalDir}/Results/$1*.success` ;
    #   do 
    #     n=`expr $n + 1`
    #     src="`basename ${ko/\.success/}`"
    #     maple -q \
    #           -c "restart" \
    #           -c "parBaseFileName:=convert(\"${src}\",string)" \
    #           -c "parJobPrefix:=convert(\"${src/[0-9\{\}]*/}\",string)" \
    #           >> ${logfile} <<END 
    #               print("***************************************************");
    #               print(parBaseFileName, parJobPrefix);
    #               read("${MyGlobalDir}/mc/Jets.s"):
    #               read(cat("${MyGlobalDir}/mc/",parJobPrefix,".init.mc")):
    #               read(cat("${MyGlobalDir}/States/",parBaseFileName,".state")):
    #               #r := JetMachine[Consequences]:-ExportGen( cat(parJobPrefix,".consequeces.txt"), parBaseFileName, "${MyGlobalDir}");
    #               #if nops(r)=0 then \`quit\` (0) else \`quit\` (1) fi;
    #               r := JetMachine[Consequences]:-TestGen(parBaseFileName, "${myfilebase}.ignore.data", "${MyGlobalDir}", parJobPrefix);
    #               print("***************************************************");
    #               if r=false then \`quit\` (0) else \`quit\` (1) fi;
    # END
    #   result=$?
    #   #echo "maple result is $result"
    #   if [[ $result -eq 0 ]] ; then
    #   	echo "$ko is general"
    #   	m=`expr $m + 1`
    #   	zip ${zipfile} $ko "${MyGlobalDir}/States/${src}.state" "${MyGlobalDir}/Logs/${src}.log"
    #   elif [[ $result -eq 1 ]] ; then
    #   	echo "$ko is a consequece"
    #   else
    #   	echo "ERROR testing of $ko"
    #   fi
    #   done
    # 
    # zip ${zipfile} ${logfile}
    # find "${MyGlobalDir}/mc/" -name "*.mc"  -print | zip  ${zipfile} -@
    # find "${MyGlobalDir}/mc/" -name "*.s"   -print | zip  ${zipfile} -@
    # 
    # echo "total $n, general $m"

    
  end module; # Consequences
end module: # JetMachine