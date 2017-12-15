
lprint("CommonProc.mc v. 0.2.j", __FILE__);

# Printing to file

writetofile := proc(filename, text)
  local fd, i;
  fd := fopen(filename, WRITE, TEXT):
  for i from 2 to nargs do fprintf(fd, "%Q\n", args[i]); end do;
  fclose(fd);
end:

write2ft := proc(filename, text)
  # write to file and terminal
  local fd, i;
  fd := fopen(filename, WRITE, TEXT):
  for i from 2 to nargs do 
    printf ("%Q\n", args[i]);
    fprintf(fd, "%Q\n", args[i]); 
  end do;
  fclose(fd);
end:


appendtofile := proc(filename, text)
  local fd, i;
  fd := fopen(filename, APPEND, TEXT):
  for i from 2 to nargs do fprintf(fd, "%Q\n", args[i]); end do;
  fclose(fd);
end:

append2ft := proc(filename, text)
  # append to file and terminal
  local fd, i;
  fd := fopen(filename, APPEND, TEXT):
  for i from 2 to nargs do 
    printf ("%Q\n", args[i]); 
    fprintf(fd, "%Q\n", args[i]); 
  end do;
  fclose(fd);
end:

DebugReport := proc()
  if detailedReportFile <> "" then
    appendtofile(detailedReportFile, args);
  else
    printf("\nDebugReport: %Q\n", args);
  fi;
end proc:


# sorting proc for RESOLVE result

`ResolveSizer/timeout` := 60:
`ResolveSizer/details` := table():


ResolveSizer := proc (R)
  description "Sorts resolve results by size, linear cases first" ;
  global `ResolveSizer/timeout`, `ResolveSizer/details`;
  local res, e, s1, s2, s3, se, sed;
  if nops(R)=3 then # linear case
      try
        s1 := size(R[1]);
        s2 := size(R[2]);
        s3 := size(R[3]);

        e := timelimit(`ResolveSizer/timeout`, Simpl(R[3]/R[1])); # the resolved expression # TODO:  may overfill memory and take looong time
        
        se := size(e);
        sed := size(denom(e));
        
        res := (s2*1e8-1e8)*(se + sed/1000 + s1/1000000 + s3/100000); 
        `ResolveSizer/details`[R] := sprintf("ResolveSizer()=%a, sizes: s1=%a, s2=%a, s3=%a, se=%a, sed=%a, w.r.t. %a",
                                              res, s1, s2, s3, se, sed, R[2]);
      catch "time expired" :    
        printf("ResolveSizer time expired: %q\n", StringTools[FormatMessage](lastexception[2..-1]));
        res := s1*s2*s3;
        `ResolveSizer/details`[R] := sprintf("ResolveSizer()=%a out of time, sizes: s1=%a, s2=%a, s3=%a, w.r.t. %a",
                                              res, s1, s2, s3, R[2]);

      catch "numeric exception: division by zero" :    
        printf("ResolveSizer failed: %q\n", StringTools[FormatMessage](lastexception[2..-1]));
        printf("Omitting this case, size=infinity");
        res := infinity;
        `ResolveSizer/details`[R] := sprintf("ResolveSizer()=%a, division by 0, sizes: s1=%a, s2=%a, s3=%a, se=%a, sed=%a, w.r.t. %a",
                                              res, s1, s2, s3, se, sed, R[2]);     
                                          
      catch :    
        printf("Error in ResolveSizer: %q\n", StringTools[FormatMessage](lastexception[2..-1]));
        printf("Omitting this case, size=infinity");
        res := infinity;
        `ResolveSizer/details`[R] := sprintf("ResolveSizer() error: %a", StringTools[FormatMessage](lastexception[2..-1]));  
      end try; 
      return res;  
  else 
    infinity # nonlinear case
  fi  
end:

### getting unknowns of specifyed expression
# define sortedUnks() to force resolving w. r. to ALL unks (instead of declared unknowns)
#
# Example:
#
#sortedUnks := proc (expr)
#  description "Returns  `unk/<</list` union (unks(expr) minus `unk/<</list`)";
#  global `unk/<</list`;
#  # maple predefined union and minus is unusable becouse operates on sets only, 
#  # the order is important here  
#  [ op(`unk/<</list`), 
#    op( map (proc (x) if not x in `unk/<</list` then x fi end proc, unks(expr)))
#  ]
#end proc:

if assigned(sortedUnks) then
  `ForceAllUnksResolving/GenerateResultFiles` := true; #  if true, resolving w. r. to ALL unks (instead of declared unknowns) is forced (using sortedUnks())
  print("`ForceAllUnksResolving/GenerateResultFiles` enabled. During the forking stage, resolving w. r. to ALL unks enforced. Using sortedUnks().");
else
  `ForceAllUnksResolving/GenerateResultFiles` := false;
fi:


# Generators of .runme file:

GenerateResultFiles := proc (basefilename::string, StateFilesDir::string, RunMeFilesDir::string, NonlinearFilesDir::string, $)
  description "Generates result files when Run() failed";
  # StateFilesDir: dir path to the States dir relative to pwd of .mc whitch reads generated .runme file, usually  "global/States/"
  # RunMeFilesDir: relative path to dir where .runme files are to be stored, usually  "Ready/"	
	GenerateFailedResultFiles(basefilename, StateFilesDir, RunMeFilesDir, NonlinearFilesDir, 0); 
end:

GenerateFailedResultFiles := proc(basefilename::string, StateFilesDir::string, RunMeFilesDir::string, NonlinearFilesDir::string, stepnumber::integer, $)
  global RESOLVE, ressize, `ResolveSizer/details`;
  local resolveResult, sortedFailedResolve, failedResult, a1, b1, x1, a1_der, a1_lin, r1 ;
  printf("----------------------------------------\nResolve failed at level %a.\n", stepnumber);
  #printf("RESOLVE=%a\n", RESOLVE);
  if nops(RESOLVE) = 0 then
    DebugReport("GenerateFailedResultFiles[%a] Error: Empty RESOLVE. ressize=%a too low? All consequent forks are not generated!\n", stepnumber, ressize);
    # TODO: create some explicit file to inform the user about this accident!!!
    printf("Instead of return, let the code bellow generate ""invalid subscript selector"" error, "); 
    printf("which will be catched together with all already generated .runme files. \n");
    printf("User may increase ressize and try again.\n");
  fi;
  sortedFailedResolve := sizesort(convert(RESOLVE,'list'), ResolveSizer);
  DebugReport(sprintf("GenerateFailedResultFiles(%a): sorted RESOLVE=%Q", stepnumber, sortedFailedResolve));
	printf("***** sortedFailedResolve: *****\n");
	map (
	 proc (x) 
	   if nops(x)=3 then
       printf("\n* linear (%a): \n%a\n", x[2], `ResolveSizer/details`[x]);
       lprint("x[1]"=x[1]);
       lprint("x[2]"=x[2]);
       lprint("x[3]"=x[3]);
	   else 
      printf("\n* NONlinear(%a)\n", x[2]);
      lprint("x[1]"=x[1]); 
      lprint("x[2]"=x[2]);
      fi;
	 end proc, 
	 sortedFailedResolve);
	printf("***** end of sortedFailedResolve listing *****\n");
	failedResult := sortedFailedResolve[1];
	#printf("failedResult=%a\n\n", failedResult);
	if nops(failedResult)=2 then
      # nonlinear failure
      a1:=failedResult[1]; # nonlinear expression
      x1:=failedResult[2]; # the unknown
      printf("NONLINEAR failure.\n");
      if type(a1, nonzero) then
        printf("\nError: type(E%a, nonzero)=true. Attempt to Nonlinear failure on nonzero expression is skipped.\n", stepnumber);
      else  
         printf("*** NONLINEAR failure. Generating nonlinfail file.\n", stepnumber);
         GenerateNonLinFailFile(sortedFailedResolve, basefilename, StateFilesDir, RunMeFilesDir, NonlinearFilesDir, stepnumber+1);             
      fi;
	else
      # linear failure  a1*x1=b1 where x1 is unknown to be resolved
      a1:=failedResult[1];
      b1:=failedResult[3];
      x1:=failedResult[2]; 
      printf("Lets generate result files based on the expression E%a:\n", stepnumber);
      print(a1); 
      printf("E%a=%q\n", stepnumber, a1);
      GenerateNonZeroFile(a1, basefilename, StateFilesDir, RunMeFilesDir, stepnumber);  
      GenerateNextResultFiles(a1, basefilename, StateFilesDir, RunMeFilesDir, NonlinearFilesDir, stepnumber+1);
    fi;      
end:


GenerateNextResultFiles := proc(expr, basefilename::string, StateFilesDir::string, RunMeFilesDir::string, NonlinearFilesDir::string, stepnumber, $)
  local resolveResult, u, ratio;
  global ressize, putsize, maxsize, `ForceAllUnksResolving/GenerateResultFiles`;

  printf("\n----- %a\nresolve(E%a)", stepnumber, stepnumber);
  u := `unk/<</list` ; # store actually used unknowns
  try
    if `ForceAllUnksResolving/GenerateResultFiles` then unknowns(op(sortedUnks(expr))); fi ; # use unknowns from expression to be resolved
    resolveResult := resolve(expr); 
    
    if evalb(`resolve/result/type`='Fail') 
        and evalb(`resolve/result/suppressedminsize` <> NULL) then
      
      ratio := `resolve/result/suppressedminsize`/maxsize*2;
      
      printf("\nTrying to increase sizes by ratio %a:\n", ratio);
      printf("resolve(E%a)",stepnumber);
      
      ressize := trunc(ressize*ratio);  putsize := trunc(putsize*ratio);  maxsize := trunc(maxsize*ratio);
      
      resolveResult := resolve(expr);

    fi;

    printf("=\n");
    print(resolveResult);    
  catch "no unknowns":
    printf("\n%q\n", lastexception);
    #resolveResult := (expr=0);
    #printf("Resolve reported \"no unknowns\" failure, lets try just put(%a):\n", resolveResult);     
    resolveResult := 'CE';
    printf("Resolve reported \"no unknowns\" failure, nothing to do. The unknownless expression is %a\n", expr);    
  catch "there are contradictory equations":
    resolveResult := 'CE' ;
    printf("there are contradictory equations.\n");
  finally 
    if `ForceAllUnksResolving/GenerateResultFiles` then unknowns(op(u)); fi; # restore originally used unknowns  
  end try;
  
  if resolveResult = FAIL then
    GenerateFailedResultFiles(basefilename, StateFilesDir, RunMeFilesDir, NonlinearFilesDir, stepnumber); 
  elif  resolveResult = 'CE' then
    print("1=0, nothing to do.");
  else
    GeneratePutZeroFile(resolveResult, basefilename, StateFilesDir, RunMeFilesDir, 2*stepnumber);  	  
    # GeneratePutZeroFile(x1=b1/a1, basefilename, StateFilesDir, RunMeFilesDir, stepnumber);
  fi;
end:


WriteRunmeFile := proc (fileName::string, basefilename::string, StateFilesDir::string, expr2run::list(list), {message::string:=""}, $)
  global ressize, putsize, maxsize;
  writetofile(fileName, cat(op(map(sprintf@op, [
     # log startup
     ["printf(""Here is file: '%s'\\n"");\n", fileName],
     # (optional) current state
     [ "if not(assigned(previousStateFile)) and (assigned(`readstate/put/limit/size`)  or assigned(`readstate/put/limit/length`) ) then \n\
          previousStateFile := ""%s/%s.state""; \n\
          if type(`readstate/put/limit/size`,   numeric) then `put/limit/size`:=`readstate/put/limit/size`;   fi;\n\
          if type(`readstate/put/limit/length`, numeric) then `put/limit/length`:=`readstate/put/limit/length`; fi;\n\
          lprint(""Reading "", previousStateFile);\n\
          read(previousStateFile); \n\
          lprint(""Done "", previousStateFile);\n\
          unassign('`put/limit/size`', '`put/limit/length`');\n\
       fi;\n", StateFilesDir, basefilename],
     # previous .runme chain
     ["read( ""global/Done/%s.runme"" );\n", basefilename],
     # fix current dependence()	      			
     ["dependence(%a);\n", dependence()],       
     # preserve size opts
     ["ressize := %a; putsize := %a; maxsize := %a;\n", ressize, putsize, maxsize],
     # optional message
     `if`(message="", NULL, ["lprint(%a);\n", message]),
     # NEW JOB INITIAL DATA
     ["\n%s\n", cat(op(map(sprintf@op, expr2run)))], # expr2run = [["format", data, ...], ...]
     # log finish
     ["printf(""Finished file: '%s'\\n"");\n", fileName],
     # mark .runme file as done
     ["# Done"]]))))
end:

GenerateNonZeroFile := proc (resolvedExpr, basefilename::string, StateFilesDir::string, RunMeFilesDir::string, stepnumber::integer, $) 
  global ressize, putsize, maxsize, `nonzero/hasnew`;
  local fileName ;
  printf("GenerateNonZeroFile[%a]\n",stepnumber); 
  if type(resolvedExpr, nonzero) then
    printf("GenerateNonZeroFile[%a]: WARNING, argument to nonzero(%a) is already declared as nonzero. Skipping generating nonzero file!!!\n", stepnumber, resolvedExpr);
    return;
  fi;
  fileName := cat(RunMeFilesDir, basefilename, sprintf("%s", WrapNumber(stepnumber*2+1)), ".runme") ;
  printf("Generating nonzero file %s: nonzero(E%a);\n", fileName, stepnumber) ;
  WriteRunmeFile (fileName, basefilename, StateFilesDir, [
                  ["`nonzero/old`:=`nonzero/s`;\n"],
                  ["nonzero (%a);\n", resolvedExpr],
                  ["`nonzero/hasnew` := evalb(`nonzero/old`<>`nonzero/s`);\n"]]);
end:

GeneratePutZeroFile := proc (resolvedExpr, basefilename::string, StateFilesDir::string, RunMeFilesDir::string, stepnumber::{integer,string}, {message::string:=""}, $) 
  global ressize, putsize, maxsize, `JetMachine/opt/suppressPuts`;
  local fileName ;
  printf("GeneratePutZeroFile[%a] %s\n", stepnumber, message); 
  fileName := cat(RunMeFilesDir, basefilename, WrapNumber(stepnumber), ".runme") ;
  if type(lhs(resolvedExpr)-rhs(resolvedExpr), nonzero) then
    printf("GeneratePutZeroFile[%a]: Argument to be put is already declared as nonzero, generating of %a skipped.\n", stepnumber, fileName);
    lprint("put:", resolvedExpr);
    lprint("divideout:", divideout(lhs(resolvedExpr)-rhs(resolvedExpr)));
    return;
  fi;
  if not(assigned(`JetMachine/opt/suppressPuts`)) or `JetMachine/opt/suppressPuts`<> true then 
    printf("Generating putzero file %s: put(%a); \n", fileName, resolvedExpr) ;
    WriteRunmeFile (fileName, basefilename, StateFilesDir, [
                    ["unassign('`nonzero/hasnew`');\n"],
                    ["try\n"], 
                    ["put(%a); \n", resolvedExpr],
                    ["catch:   lastlastexception := lastexception;\n"],
                    ["end try;\n"]],
                    ':-message'=message);
  else
    printf("SUPPRESSED generating putzero file %s: put(%a); \n`JetMachine/opt/suppressPuts`=%a\n", fileName, resolvedExpr,`JetMachine/opt/suppressPuts`) ;
  fi;
end:

GenerateContinueFile := proc (basefilename, StateFilesDir, RunMeFilesDir, stepID, ContinuingCommand, $) 
  global ressize, putsize, maxsize;
  local fileName ;
  fileName := cat(RunMeFilesDir, basefilename, stepID, ".runme") ;
  printf("Generating continue file %s: %A \n", fileName, ContinuingCommand) ;
  writetofile (fileName, 
    sprintf("%A\n%A\n%A\n# Done",
      cat("read( """, StateFilesDir, basefilename, ".state"" ); "),
      sprintf("ressize := %a; putsize := %a; maxsize := %a;\n", ressize, putsize, maxsize),
      ContinuingCommand));
end:

GenerateNonLinFailFile := proc (sortedResolve, basefilename::string, StateFilesDir::string, RunMeFilesDir::string, NonlinearFilesDir::string, stepnumber::integer, $) 
  global ressize, putsize, maxsize;
  local fileName, step1, step2, Fs, F1, NL, s, ss;
  fileName := cat(NonlinearFilesDir, basefilename, ".nonlinfail") ;  
  printf("\n*****\nNonlinear failure!!!\nGenetating %a\nsortedResolve=%a\n", fileName, sortedResolve);
  writetofile (fileName, 
    sprintf("#sortedResolve=%a\n%A\n%A\nprint(\"And what now?\");\n",
      sortedResolve,
      cat("read( """, StateFilesDir, basefilename, ".state"" ); "),
      sprintf("ressize := %a; putsize := %a; maxsize := %a;\n", ressize, putsize, maxsize)));
      
  # factorize
  step1 := 0;
  Fs := map(proc(R)
              local f, NLrem, Lins;
                step1 := step1 + 1;
                NLrem := 1;
                f := factors(R[1]);
                if nops(f[2]) = 1 then # not factorized
                  append2ft (fileName,  sprintf("# sortedResolve[%a] not_factorized, %a, %a, %a\n", step1, nops(f[2]), R[2], f[1]));
                  return [[], R[1]];
                else # factorized
                  append2ft (fileName,  sprintf("# sortedResolve[%a] YES_FACTORIZED, %a, %a, %a*%q\n", step1, nops(f[2]), R[2], f[1], f[2]));
                  Lins := map(proc(E)
                                local e, res, LV;
                                e := simpl(E[1]); # E[1]^E[2]=0 <=> E[1]=0
                                LV := LVar(e);
                                if type(e, linear(LV)) then # linear factor found
                                    append2ft (fileName,  sprintf("# sortedResolve[%a] LINEAR_FACTOR_FOUND: LVar=%a, (%a)^(%a)=0\n", step1, LV, e, E[2]));
                                    if LV<>R[2] then 
                                      append2ft(fileName, 
                                                sprintf("# sortedResolve[%a] LINEAR_FACTOR_FOUND: Leading var %a of resolved expression is not %a.\n", 
                                                step1, LV, R[2])) 
                                    fi;
                                    try
                                      res := resolve(e);
                                    catch:
                                      append2ft (fileName,  sprintf("# sortedResolve[%a] LINEAR_FACTOR_RESOLVE_FAIL %a\n%q\n", 
                                                                    step1, StringTools[FormatMessage](lastexception[2..-1])));    
                                      NLrem := NLrem*e;
                                      return NULL;                
                                    end; 
                                    if res=FAIL then
                                      append2ft (fileName, sprintf("# sortedResolve[%a] LINEAR_FACTOR_RESOLVE_FAIL (%a)\n", step1, res));
                                      NLrem := NLrem*e;
                                      return NULL;
                                    else
                                      append2ft (fileName, sprintf("# sortedResolve[%a] LINEAR_FACTOR_RESOLVED %a\n", step1, res));
                                      return res;  
                                    fi;                                                               
                                else
                                    append2ft (fileName,  sprintf("# sortedResolve[%a] non_linear_factor_found: LVar=%a, (%a)^(%a)=0\n", step1, LV, e, E[2]));                
                                    NLrem := NLrem * e;
                                    return NULL;
                                fi;
                              end, f[2]);                      
                  if type(NLrem, constant) then 
                    append2ft (fileName, sprintf("\nsortedResolve[%a] Remaining CONSTANT nonlinear term is %a\n", step1, NLrem));
                    # TODO: stop treating the rest of nonlinear terms now, we do not need it!
                  else
                    append2ft (fileName, sprintf("\nsortedResolve[%a] Remaining nonlinear term is \n%a\n", step1, NLrem));         
                  fi;
                  
                  printf("sortedResolve[%a] size is %q\n", step1, `GenerateNonLinFailFile/size`([Lins,NLrem]));
                  return [Lins, NLrem];
                fi;
              end,
            sortedResolve);
  append2ft (fileName, sprintf("# We have %a linear factors\n", map(R->nops(R[1]), Fs)));
  append2ft (fileName, sprintf("# with nonlinear remainders of sizes %a\n", map(R->size(R[1]), Fs)));
  append2ft (fileName, sprintf("# Total sizes are %a\n", map(`GenerateNonLinFailFile/size`, Fs)));
  
  # choose the best nonlinear failure
  Fs := sizesort(Fs, `GenerateNonLinFailFile/size`); # TODO: We are looking for minimum AND we need to know the index of item choosed
  F1 := Fs[1];
  NL := F1[2];
  append2ft (fileName, sprintf("# Won %a\n", `GenerateNonLinFailFile/size`(F1)));
  append2ft (fileName, sprintf("# Nonlinear term remaining is %q\n\n", NL));  
  
  # generate *.runme files
  step2 := 0;
  map(proc(L)
        step2 := step2 + 1;
        GeneratePutZeroFile(L, basefilename, StateFilesDir, RunMeFilesDir, cat("0", WrapNumber(2*step2)), message="NONLINFAIL_FACTOR");
      end, 
      F1[1]);

  # lets try solve remaining nonlinear expression
  # TODO: Lets try to solve ALL and choose the solved as the best
  if NL <> 1 then 
    s := `GenerateNonLinFailFile/solver`(NL);
    # TODO: filter out contradictions to nonzero
    if s = [] then 
      append2ft (fileName, sprintf("solver: no solutions found for nonlinear term selected\n"));
      append2ft (fileName, sprintf("solver: Applying solver to REMAINING nonlinear terms (NOT USING IT!):\n"));
      ss := map(`GenerateNonLinFailFile/solver`, Fs[2..-1]);
      map(s -> append2ft (fileName, sprintf("%a\n\n", s)), ss);
    else
      append2ft (fileName, sprintf("solver: Found %a solutions for nonlinear term selected:\n", nops(s)));
      append2ft (fileName, sprintf("%a\n\n", s));

      # generate .runme files
      map(proc(e)
            step2 := step2 + 1;
            if lhs(e)=rhs(e) then  
              append2ft (fileName, sprintf("solver: Error: %a\n", e)); 
            else
              GeneratePutZeroFile(e, basefilename, StateFilesDir, RunMeFilesDir, cat("0", WrapNumber(2*step2)), message="NONLINFAIL_SOLVE");
            fi;
          end, s);
    fi;  
  fi;

  # lets try linderive on the remaining nonlinear term 
  LinderiveOnNonLin(NL, fileName); 
end:

`GenerateNonLinFailFile/size` := proc(F::list)
    local Lins, NLrem, L;
    Lins, NLrem := op(F);
    return ((size(NLrem))*10^12 # size of nonlinear factor 1 must be 0
            + add(size(L), L in Lins));
end:

`GenerateNonLinFailFile/solver` := proc(expr)
  local sol, LV;
  LV := LVar(expr);
  sol := [solve(expr, LV)];
  sol := remove(has, sol, RootOf);
  return map(s->LV=simpl(s), sol); # simplify(e, symbolic) ?
end:

LinderiveOnNonLin := proc(expr, nonLinFailFileName::string, $)
  local ld, lin, LV;
   # linearize by linderive
    LV := LVar(ld);     
    printf("*** applicating linderive (in %a)\n", LV);
    ld := linderive(expr);
    printf("linderive given totally %a results\n", nops(ld));
    ld := map(divideout@Simpl, ld);
    ld := remove(proc(a) evalb(a = 0) end, ld); # remove trivial eqs ### we have removed also evalb(a = 1) in the past  

    lin := select(type, ld, linear(LV));
    if nops(ld)=nops(lin) then
      append2ft(nonLinFailFileName, sprintf("linderive given %a nontrivial results, all of them are linear:\n", nops(ld)));
    else
      append2ft(nonLinFailFileName, sprintf("linderive given %a nontrivial results, just %a of them are linear:\n", nops(ld), nops(lin)));
    fi;

    if nops(lin) > 0 then 
      lin := sizesort([op(lin)], size);
      map2(append2ft, nonLinFailFileName, lin);
      append2ft(nonLinFailFileName, sprintf("TODO: Generate .runme file extended by all linear eqs.")); # TODO!!!
    else
      append2ft(nonLinFailFileName, sprintf("linderive given nonlinear results only:\n%q.\n", ld));
    fi;
end:

WrapNumber := proc(number::{integer,string}, $)
  description "Returns numeric argument as a string wrapped by {} when >=10";
  if type(number,string) then # do not change strings
    number
  else
    if number > 9 then sprintf("{%a}", number) else  sprintf("%a", number) fi
  fi;
end :



###
### Auxiliary  procedures
###

ReportSuccessState := proc(parBaseFileName::string, p2, $) 
	description "Reports jets's state in human readable format to given file and to terminal";
	local filename, title;
  if nargs>1 then title := args[2] else title := "" fi;
	
	# report to terminal
  PrintSuccessReport(title);
  
  if nargs >= 2 then
    # report to file Results/<parBaseFileName>.success
    filename := cat("Results/", parBaseFileName, ".success");	
    try
      appendto(filename);   
      PrintSuccessReport(parBaseFileName, title);
    finally
      writeto(terminal);
    end try;
	fi;
end: 

PrintSuccessReport := proc (parBaseFileName::string, p2, $)
  local title;
  if nargs>1 then title := args[2] else title := "" fi;
  printf("\n--------------------\nSuccess report(%a): %Q\n", parBaseFileName, title);
  
  printf("Varordering=%a, ressize=%a, putsize=%a, maxsize=%a, ccmethod=%a, dmethod=%a, %a MB allocated.\n\n", 
           `Var/<</opt`,ressize, putsize, maxsize, ccmethod, dmethod, toMB(kernelopts(bytesalloc)));
  
  printf("\n*** dependence() =\n");
  print(    dependence()); 
  
  printf("\n***  nonzero() =\n");
  print(     nonzero()); 
  
  printf("\n*** \n");
  map(a -> printf("%a=%q\n", op(a), eval(op(a))), [indices(`dep/tab`)]);
      
  printf("\n*** cc() = %q\n", cc());
  
  
  #printf("\n*** map(simpl@evalTD@eval,[S]) =\n"); # if S is array or mytrix, does not work properly
  #print(    map(simpl@evalTD@eval,[S]));
  
  if assigned(PrintUserSuccessReport) then 
    printf("\n--------------------\n"); 
    try
      PrintUserSuccessReport(); 
    catch:
      printf("Warning, PrintUserSuccessReport() failed: %q\n", 
          StringTools[FormatMessage](lastexception[2..-1]));
    end:  
  fi;
    
  printf("\n-------------------- End of success report\n");
end proc:

# The user can define anywhere the custom report :
#
# PrintUserSuccessReport := proc()
#   print('A'=map(eval@simplify, op(A)));
#   print('B'=map(eval@simplify, op(B)));
# end:


sprintEV := proc (expr)
  description "returns string expr=value, where value is evaluated expr.";
  option inline;
  sprintf("%a=%q",'expr',eval(expr))
end proc:

printEV := proc(expr)
  description "prints expr=value, use [expr1, ..., exprn] for multiple arguments";
  option inline;
  `if` (type('expr',list),
    printf("%Q\n", op(map('sprintEV','expr'))),
    printf("%Q\n", sprintEV('expr')));
end proc:



ListUnion := proc ()
  map(op , [args])
end:




UpdateAliasSubs := proc()
global `dsolveMyZ/substitutions`;
  local aliaslist, maxdegree;
  aliaslist := [alias()];
  maxdegree :=  `if`( nargs>=1 and type(args[1],posint), min(args[1], nops(aliaslist)), min(9, nops(aliaslist))); 
  `dsolveMyZ/substitutions` := 
    map(
      proc(a) 
        local pa; 
        pa := parse(a,statement); 
        `if`(type (pa, specfunc(anything,jet)),pa=cat(a, _), NULL) # do not add dependent u_* to substitutions
      end, 
      [alias()][-maxdegree..-1])
end:

ConvertArgsDd := proc()
  description "Diff to diff vars conversion (jet u_x to unassigned u_x_)";
  global `dsolveMyZ/substitutions`;
  op(map(a -> 
          map(convert, a, diff, op(`dsolveMyZ/substitutions`)), 
        [args]));
end:


ConvertArgsdD := proc()
  description "diff to Diff vars conversion (unassigned u_x_ to jet u_x)"; 
  # conversion of jet vars implimented yet ONLY
  global `dsolveMyZ/substitutions`;
  op(map(a -> subs( op(map(a -> op(2,a) = op(1, a), `dsolveMyZ/substitutions`)), a), [args]));
end:

Dsolve := ConvertArgsdD@dsolve@ConvertArgsDd:
PDsolve := ConvertArgsdD@pdsolve@ConvertArgsDd:


`dsolveMyZ/timelimit` := 2: # limit in seconds for each single dsolve call
`dsolveMyZ/method` := Dsolve: # pdsolve also possible
`dsolveMyZ/printerrors` := false:

`dsolveMyZ/substitutions` := []:

dsolveMyZ := proc (Z)
  description "Try to dsolve the result of clear(pds)";
  global `dsolveMyZ/timelimit`, `dsolveMyZ/method`;
  local unknowns;
  unknowns := map2(op, 1, [dependence()]) ;
  print(op(map(ConvertArgsDd, unknowns)));
  # try dsolve all nonzero items of Z w. r. to all possible unknowns
  map(
      proc(ZZ) 
        local result;
        if simplify(ZZ) <> 0 then
          # take a nonzero item of Z
          if length(ZZ) < 500 then printf("***\n"); print(ZZ); else printf("*** Equation too long (%q).\n", length(ZZ)); fi;
          map (
            proc (unk)  
              try 
                # take an unknown
                result :=  timelimit(`dsolveMyZ/timelimit`, `dsolveMyZ/method`(ZZ, unk)); 
                printf("* %q\n", unk);
                print(result);
                result;
              catch "time expired":
                printf("* %q time expired\n", unk);
              catch : 
                if `dsolveMyZ/printerrors`=true then printf("* %a: %q\n", unk, StringTools[FormatMessage](lastexception[2..-1])); fi;
              end try; 
            end proc
            ,
            unknowns
            )    
        fi;
      end proc
    ,
    Z
  );
# map(x -> map(y -> print(op(1,y), map(z -> value(z), selectfun(op(2,y), Int))),x) , koko):

end proc: 



#
# Importantness of current state
#

ThrowExceptionWhenNonImportant := proc()
  description "Throws an exception when current state is unmimportant" ;
  local e ;
  e := TestOfNonImportantness();
  if e <> NULL then
     error "TestOfNonImportantness failed", e 
  fi
end proc:

TestOfNonImportantness := proc()
  description "Returns NULL if current state is important. Implicitly returns NULL everytime." ;
  ## by default, returns NULL every time (so everything is important)
  NULL
  ## Redefine this function to change importantness behavior
  ## Example:
  # local d;
  # d := `union`(op(map(vars,{A[1,1], A[1,2], A[2,2]} union {B[1,1], B[1,2], B[2,2]})));
  # if d subset {x,y} then
  #       print("TestOfNonImportantness failed, ", d);
  #       "Not enough variables." 
  # else
  #   print("TestOfNonImportantness ok, ", d);
  #   NULL
  # fi
  ##
end proc:

`TestOfNonImportantness/IsZeroMatrix` := proc(A::{table,array})
  andmap(proc(i)
            local a;  
            a := simpl(eval(A[op(i)])); 
            A[op(i)] := a;  # store simplified items
            return(a=0) 
        end, 
        [indices(A)])
end:

