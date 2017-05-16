lprint("SingleStep.mc v. 0.2.h", __FILE__);
# Initialization
StateFilePath := cat("States/", parBaseFileName, ".state"):
printf ("\nParameters:\nparBaseFileName=%a, parCD=%a, parJobPrefix=%a\n\n", 
          parBaseFileName, parCD, parJobPrefix);
          
PrintFileInfo := proc(my_file)
  try
    printf("Using %s. Abs. path:  %s, mod. time: %s, size: %a B.\n",
      my_file,
      FileTools[AbsolutePath](my_file),
      StringTools[FormatTime]("%d. %m. %Y, %H:%M:%S", timestamp=FileTools[ModificationTime]( my_file )),
      FileTools[Size]( my_file));
  catch:
      printf("Error while getting file %s info:%q\n", my_file, StringTools[FormatMessage](lastexception[2..-1]));
  end try;     
end:

try #WSParser:Skip#
  interface(labelling=false);
  read `global/mc/Jets.s`;
  read `global/mc/CommonProc.mc`;
  PrintFileInfo(`global/mc/Jets.s`);
  PrintFileInfo(`global/mc/CommonProc.mc`);
  PrintFileInfo(`global/mc/SingleStep.mc`); # this file
  
catch: 
  printf("Error, initialization failed:%Q\n", 
      StringTools[FormatMessage](lastexception[2..-1]));
  `quit` (51);
end try;

detailedReportFile := cat("Logs.Detailed/",parBaseFileName,".log") ;
#reportfile := cat("Logs.Detailed/",parBaseFileName,".r.log") ;

try #WSParser:Skip#
  my_file := sprintf("global/mc/%s.init.mc", parJobPrefix);
  PrintFileInfo(my_file);
  read  my_file; #WSParser:Parse#
catch:
  printf("Error while reading mc/%s.init.mc:%Q\n", 
    parJobPrefix, StringTools[FormatMessage](lastexception[2..-1]));
   `quit` (52);
end try; 

#printlevel := 4; #WSParser:Skip#
#kernelopts(datalimit=(kernelopts(datalimit)-5*1024)); #WSParser:Skip#
#reporting(pd = 5, cc = 5, derive = 5, run = 5, resolve = 5); #WSParser:Skip#
  
## read data from previous steps
#try
#  if type(`readstate/put/sizelimit`, numeric) and type(previousStateFile, string) then
#    `put/sizelimit`:=`readstate/put/sizelimit`;
#    printf("Reading previousStateFile file %a with `put/sizelimit`=%a...\n", previousStateFile, `put/sizelimit`);
#    read(previousStateFile);
#    printf("Done reading previousStateFile file %a \n", previousStateFile);
#    # div 0 test
#    printf("dependence() = %q\n", dependence()); ## tady ma byt try a test zda se nedeli nulou, pokud ano skoncit!
#    printf("nonzero() = %q\n", nonzero());    
#  fi;
#catch: 
#  printf("Error: Reading previousStateFile %a failed:\n", previousStateFile);
#  print(StringTools[FormatMessage](lastexception[2..-1]));
#  writetofile(cat(parBaseFileName,  ".err"), 
#      sprintf("Error reading previousStateFile: %q\n",StringTools[FormatMessage](lastexception[2..-1])));
#  `quit` (62);
#finally:
#  unassign('`put/sizelimit`');
#end try;

# Read initial data - THE CURRENT JOB
try #WSParser:Skip#
  my_file := sprintf("%s.runme", parBaseFileName);
  PrintFileInfo(my_file);
  read my_file; #WSParser:Parse#Deep#  
  printf("File %s read done.\n", my_file);
  if assigned(lastlastexception) then 
    print(".runme failed:"); 
    error lastlastexception; 
  fi; 
  # div 0 test
  printf("dependence() = %q\n", dependence()); ## tady ma byt try a test zda se nedeli nulou, pokud ano skoncit!
  printf("nonzero() = %q\n", nonzero());
catch: 
  # errors throwed inside read() statement are NOT catched by maple!
  printf("read(%a) put/nonzero failed:\n", my_file);
  print(StringTools[FormatMessage](lastexception[2..-1]));
  writetofile(cat(parBaseFileName,  ".err"), 
      sprintf("Error: %q\n",StringTools[FormatMessage](lastexception[2..-1])));
  `quit` (53);
end try;

# test whether .rumne nonzero given something new to avoid infinity loops (if apply)
if assigned(`nonzero/hasnew`) and `nonzero/hasnew`=false then
  print("nonzero is not giving new data");
  printf("nonzero() = %q\n", nonzero());
  #writetofile(cat(parBaseFileName,  ".err"), "Forking: nonzero in .runme is not giving new data.\n");
  ## TODO: instead of error, create Abandoned file?
  print ("Done");
  `quit` (61);
fi;


# Run computations  
try
  # div 0 test
  printf("dependence() = %q\n", dependence()); ## tady ma byt try a test zda se nedeli nulou, pokud ano skoncit!
  printf("nonzero() = %q\n", nonzero());
  #
  printf ("`Var/<</opt`=%a\n", `Var/<</opt`);
  printf ("`unk/<</list`=%q\n",`unk/<</list`);
  
  printf("\n# Lets do 'run(S);'...\n");
  run(S);
  printf("\n# 'run(S);' is done.\n");
  ThrowExceptionWhenNonImportant();
  
  if evalb(assigned(`resolve/result/suppressedminsize`) and `resolve/result/suppressedminsize` <> NULL) then
    ratio := `resolve/result/suppressedminsize`/maxsize*2;
    printf("Trying to increase sizes by ratio %a.\n", ratio);
    ressize := trunc(ressize*ratio);  putsize := trunc(putsize*ratio);  maxsize := trunc(maxsize*ratio);
    printf("ressize=%a, putsize=%a, maxsize=%a\n", ressize, putsize, maxsize);  
    run(S);
    printf("\n# resized 'run(S);' is done.\n");
    ThrowExceptionWhenNonImportant();
  fi;  

  printf ("\n\n-----------------------------------------\n");
  printf(" `Var/<</opt`=%a, ressize=%a, putsize=%a, maxsize=%a, ccmethod=%a, dmethod=%a, %a MB allocated.\n\n", 
           `Var/<</opt`,ressize, putsize, maxsize, ccmethod, dmethod, toMB(kernelopts(bytesalloc)));
  
  printf("\n*** dependence() =\n");
  print(    dependence()); 
  
  printf("\n***  nonzero() =\n");
  print(     nonzero()); 
  
  printf("\n*** \n");
  map(a -> printf("*   %a=%q\n", op(a), eval(op(a))), [indices(`dep/tab`)]):
  printf ("\n-----------------------------------------\n\n");


catch "TestOfNonImportantness failed" :
    try #WSParser:Skip#
      printf("Nonimportant state.\n");
      writetofile( cat("Abandoned/", parBaseFileName, ".nonimportant"), 
         "dependence", dependence(), "nonzero", nonzero(),
         map(a -> sprintf("%a=%q\n", op(a), eval(op(a))), [indices(`dep/tab`)])
         #,sprintf("%q\n", StringTools[FormatMessage](lastexception[2..-1]))
            );  
      writetofile(StateFilePath, "# Done");  	
      print ("Done");
      `quit` (7);
    catch:
    	printf("writetofile %s.nonimportant failed:%q\n", parBaseFileName, 
    	   StringTools[FormatMessage](lastexception[2..-1]));
    	writetofile(cat(parBaseFileName , ".err"), 
    	   sprintf("Error: %q\n",StringTools[FormatMessage](lastexception[2..-1])));
    	`quit` (55);
    end try ;  


catch "declared nonzero became zero":
    try #WSParser:Skip#
     printf("Nonimportant state: declared nonzero became zero.\n");
    	writetofile( cat("Abandoned/", parBaseFileName, ".non0to0"), RESOLVE);  
    	writetofile(StateFilePath, "# Done");  	
    	print ("Done");
    	`quit` (8);
    catch:
    	printf("writetofile %s.ce failed:%q\n", parBaseFileName, 
    	   StringTools[FormatMessage](lastexception[2..-1]));
    	writetofile(cat(parBaseFileName , ".err"), 
    	   sprintf("Error: %q\n",StringTools[FormatMessage](lastexception[2..-1])));
    	`quit` (55);
    end try ;  
      
catch "there are contradictory equations" :
    try #WSParser:Skip#
     printf("Nonimportant state: there are contradictory equations.\n");
    	writetofile( cat("Abandoned/", parBaseFileName, ".ce"), RESOLVE);  
    	writetofile(StateFilePath, "# Done");  	
    	print ("Done");
    	`quit` (2);
    catch:
    	printf("writetofile %s.ce failed:%q\n", parBaseFileName, 
    	   StringTools[FormatMessage](lastexception[2..-1]));
    	writetofile(cat(parBaseFileName , ".err"), 
    	   sprintf("Error: %q\n",StringTools[FormatMessage](lastexception[2..-1])));
    	`quit` (55);
    end try ;  

catch "numeric exception: division by zero" :    
    printf("Run failed: %q\n", StringTools[FormatMessage](lastexception[2..-1]));
    #printf("eqn/list=\n");
    #print(`eqn/list`); 
    printf("nonzero/s=%q\n", `nonzero/s`);
    print(`nonzero/s`);      
    printf("refresh/eqn/list=\n");
    print(`refresh/eqn/list`); 
    printf("refresh/nonzero/s=\n");
    print(`refresh/nonzero/s`); 
      
    try #WSParser:Skip#
      reportfilename := cat("Results/", parBaseFileName, ".divbyzero");
    	writetofile( reportfilename, 
    	   "Division by zero.\nRESOLVE, nonzero/s, refresh/eqn/list, refresh/nonzero/s: \n", 
         RESOLVE, `nonzero/s`, `refresh/eqn/list`, `refresh/nonzero/s`);
      writetofile(StateFilePath, "# Done");
    	print ("Done");
    	`quit` (3);
    catch:
    	printf("writetofile(%s)  failed: %q", reportfilename, 
    	   StringTools[FormatMessage](lastexception[2..-1]));
    	writetofile(cat(parBaseFileName , ".err"), 
    	   sprintf("Error: %q\n",StringTools[FormatMessage](lastexception[2..-1])));
    	`quit` (55);
    end try ; 
    
catch:
  	printf("Error: Run unexpectedly failed: %q\n", StringTools[FormatMessage](lastexception[2..-1]));
  	tracelast;
  	printf("RESOLVE=%q\n", RESOLVE);
  	map(a -> printf("%a=%q\n", op(a), eval(op(a))), [indices(`dep/tab`)]);
    writetofile(cat(parBaseFileName , ".err"), 
        sprintf("Run unexpectedly failed.\nError: %q\n",StringTools[FormatMessage](lastexception[2..-1])));
    
    store(StateFilePath);    
    `quit` (54) ;
end try;

# Store final data state
try #WSParser:Skip#  
  CheckNonZero("");
  `CheckNonZero/Set` := [];
  reduce();
  store(StateFilePath);
  appendtofile(StateFilePath, "# Done");
catch:
  printf("store (%s) failed: %q\n", StateFilePath, 
      StringTools[FormatMessage](lastexception[2..-1]));
  writetofile(cat(parBaseFileName , ".err"), 
      sprintf("store(...) failed\nError: %q\n", StringTools[FormatMessage](lastexception[2..-1])));
  `quit` (56);
end try;
    
# Handle results
try #WSParser:Skip#
  if  assigned(`resolve/result/suppressedminsize`) 
  and `resolve/result/suppressedminsize` <> NULL 
  and type (RESOLVE,set) 
  and nops(RESOLVE)=0 then
      writetofile (cat(parBaseFileName , ".err"), 
         sprintf("'maxsize'=%a is too low.\n`resolve/result/suppressedminsize`=%a\nRESOLVE=%q\n",
                  maxsize, `resolve/result/suppressedminsize`, RESOLVE));
    `quit` (60);
  fi;
  
  if type (RESOLVE,set) then
    if nops(RESOLVE)=0 then
      # success
     	ReportSuccessState(parBaseFileName, "");
      
      #if nops(cc()) > 0  # or map(normal@evalTD,[S1,S2,S3,S4,S5,S6]) != [0,0,0,0,0,0] 
      #then
      ##	# TODO: Handle this correctly!
      #	print( "Error: The result is not correct, lost cc!!!");
      #fi;      
             
      # final computations

      Z:=map(simpl,clear(pds)); ### zde by se na simpl mel dat jen nejaky rozumny cas pres timelimit a pokud se nestihne vypsat to bez sumpl-u
      printf("clear(pds)=%q\n\n", Z);
      #printf("clear(pds)=%q\n\n", map(convert, Z, diff));
     
      appendtofile(cat("Results/", parBaseFileName, ".success"), 
                   sprintf("\nclear(pds)=%Q\n",Z),
                   sprintf("\nclear(pds)=%Q\n",map(convert, Z, diff)));
                   
                   

     try
      GenerateFDRFile(parBaseFileName, "global/States/",  "Ready/");

      #   printf ("\n\n-----------------------------------------\n");
      #   printf ("\n\n\nVarordering(function, reverse, degree);\n");
      #   printf ("\n\n-----------------------------------------\n");
      #   Varordering(function, reverse, degree);
      # #  #printf("reading %s.runme again...\n", parBaseFileName); 
      # #  #read sprintf("%s.runme", parBaseFileName); #WSParser:Parse#
      # #  #printf("reading done\n");
      #   S := Z; 
      #   Z := 'Z';
      #   run(S);
      #   reduce();
      #   store(cat("States/", parBaseFileName, ".frd.state"));
      #   if nops(RESOLVE)>0 then
      #      printf("frd: RESOLVE=%q\n", RESOLVE);
      #   else # success
      #      ReportSuccessState(cat(parBaseFileName, ".frd"), 
      #        "Done Varordering(function, reverse, degree): Run(Z):");  
      #      
      #      Z:=clear(pds);
      #      
      #      append2ft(cat("Results/", parBaseFileName, ".frd.success"), 
      #        sprintf("\nclear(pds)=%Q\n",Z),
      #        sprintf("\nclear(pds)=%Q\n",map(convert, Z, diff)));   
      #           
      #   fi;
     catch:
       printf("\n\nWarning, GenerateFDRFile attempt failed: %q\n", 
                  StringTools[FormatMessage](lastexception[2..-1]));     
       # note to the standard .success file about this failure
       append2ft(cat("Results/", parBaseFileName, ".success"),
          sprintf("\n\nWarning, GenerateFDRFile attempt failed: %q\n", 
                  StringTools[FormatMessage](lastexception[2..-1])));
       `quit` (4);
     end try;       
    else
      # resolve failed
      try
        GenerateResultFiles(parBaseFileName, "global/States/", "Ready/", "Nonlinear/");  
      catch:
             printf("\n\Error in  GenerateResultFiles: %q\n", 
                  StringTools[FormatMessage](lastexception[2..-1]));   
             `quit` (57);
      end try;
    fi;
  else
    # unexpected RESULT value
    printf("\ndependence() =\n");
    print(    dependence());
    write2ft (cat(parBaseFileName , ".err"), 
      sprintf("Resolve result is not a set.\nRESOLVE=%a\n", RESOLVE));
    `quit` (58);
  fi;
catch:
  printf("\ndependence() =\n");
  print(    dependence());
  write2ft(cat(parBaseFileName , ".err"), 
    sprintf("Results handling failed.\nError: %q\n", StringTools[FormatMessage](lastexception[2..-1])));
  `quit` (57);
end try;

printf("\nkernelopts(bytesalloc)=%a, kernelopts(bytesused)=%a, kernelopts(cputime)=%a\n", 
       kernelopts(bytesalloc), kernelopts(bytesused), kernelopts(cputime)); #WSParser:Skip#
print ("Done"); #WSParser:Skip#
`quit` (0); #WSParser:Skip#


