using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Core
{
  class Translator
  {
    public static Program Translate(Program p)
    {
      // print, what p is
      Console.WriteLine();
      Console.WriteLine("Printing Program...");
      Console.WriteLine("  " + p);
      Console.WriteLine();
      
      // list all procedure and implementation names to be verified
      Console.WriteLine("Printing Procedure and Implementation Names...");
      foreach (Declaration d in p.TopLevelDeclarations)
      {
        if (d is Procedure)
          Console.WriteLine("  Procedure: " + ((Procedure)d).Name);
        else if (d is Implementation)
          Console.WriteLine("  Implementation: " + ((Implementation)d).Name);
        else
          Console.WriteLine("  Something else in TopLevelDeclarations:" + d);
      }
      Console.WriteLine();

      // here we transform the whole program
      Console.WriteLine("Transforming Program...");

      Program p_transformed = new Program();
      foreach (Declaration d in p.TopLevelDeclarations)
      {
        if (d is Procedure)
        {
          Procedure proc = (Procedure)d;
          Console.WriteLine("  Procedure: " + proc.Name + ". Nothing to transform");
          p_transformed.AddTopLevelDeclaration(proc);
        }
        else if (d is Implementation)
        {
          Implementation imp = (Implementation)d;
          Console.WriteLine("  Implementation: " + imp.Name);

          Console.WriteLine("    Transforming Implementation...");
          Console.WriteLine();
          Implementation imp_transformed = Transform(imp);
          Console.WriteLine("    Implementation Transformed");

          p_transformed.AddTopLevelDeclaration(imp_transformed);
        }
        else
        {
          Console.WriteLine("  Something else in TopLevelDeclarations:" + d);
        }
      }
      Console.WriteLine();

      // print the program text to the console
      Console.WriteLine("Printing the Program Text...");
      PrintBplFile("-", p, true, true, true);

      // print the transformed program text to the console
      Console.WriteLine("Printing the Transformed Program Text...");
      PrintBplFile("-", p_transformed, true, true, true);

      // empty program
      Program p_other = new Program();
      Console.WriteLine("Printing the Empty Program Text...");
      PrintBplFile("-", p_other, true, true, true);

      //return p_other;
      return p_transformed;

    }
    // end Translate

    private static Implementation Transform(Implementation imp)
    {
      // get all target variables names
      // get all target variables names per loop
      HashSet<string> names_of_targets = new HashSet<string>();
      Dictionary<string, HashSet<string>> names_of_targets_by_loop = new Dictionary<string, HashSet<string>>();
      foreach (BigBlock bb in imp.StructuredStmts.BigBlocks)
      {
        names_of_targets.UnionWith(GetTargetNames(bb, false));
        Collect_Target_Names_by_Loop(names_of_targets_by_loop, bb);
      }

      // Just for debugging
      // print target variables
      Console.WriteLine("      Printing Target Variables Names...");
      foreach (string s in names_of_targets)
      {
        Console.WriteLine("        " + s);
      }
      Console.WriteLine();

      // begin of the transformation 
      // here we already have the list of target variables in names_of_targets HashSet

      Implementation imp_copy = (Implementation)imp.Clone(); 

      // arguments for Implementation constructor
      
      // The first 5 can be constructed directly from imp_copy parameters

      IToken tok_transformed = new Token();          
      string Name_transformed = imp_copy.Name; 

      List<Variable> InParams_transformed = new List<Variable>();
      InParams_transformed.AddRange(imp.InParams); 

      List<Variable> OutParams_transformed = new List<Variable>();
      OutParams_transformed.AddRange(imp.OutParams);

      List<TypeVariable> TypeParameters_transformed = new List<TypeVariable>();
      TypeParameters_transformed.AddRange(imp.TypeParameters);

      // The last two List parameters to have to be  constructed iteratively element by element

      // LocVars
      List<Variable> LocVars_transformed = new List<Variable>();
      LocVars_transformed.AddRange(imp_copy.LocVars);

      // just try out for now; 
      LocVars_transformed.Add(new LocalVariable(new Token(), 
        new TypedIdent(new Token(), "my_var", new BasicType(new Token(), SimpleType.Int))));
      //here we have to add copies of target variables and boolean variables for candidate invariants
      LocVars_transformed.AddRange(Get_Target_Variables_Duplicates(imp_copy.LocVars, names_of_targets));

      // StructuredStmts
      
      // to construct the last argument to Implementation constructor (StructuredStmts)
      // we need to construct and fill in BigBlocks List
      IList<BigBlock> BigBlocks_transformed = new List<BigBlock>();
      foreach (BigBlock b in imp_copy.StructuredStmts.BigBlocks) {
        IToken t_transformed = new Token();
        string label_transformed = b.LabelName;

        //TODO
        // this should be transformed further
        List<Cmd> simpleCmds_transformed = b.simpleCmds;
        StructuredCmd ec_transformed = b.ec;
        TransferCmd tc_transformed = b.tc;

        BigBlock b_transformed = new BigBlock(t_transformed, label_transformed, simpleCmds_transformed, ec_transformed, tc_transformed);
       
        BigBlocks_transformed.Add(b_transformed);
      }

      // second argument for StructuredStmts constructor
      IToken EndCurly_transformed = new Token
      {
        val = "}"
      };

      StmtList StructuredStmts_transformed = new StmtList(BigBlocks_transformed, EndCurly_transformed);
     
      Implementation imp_transformed = new Implementation(tok_transformed, Name_transformed,
        TypeParameters_transformed, InParams_transformed, OutParams_transformed, 
        LocVars_transformed, StructuredStmts_transformed);

      return imp_transformed;
    }
    // end Transform

    // the method returns duplicates of all target variables
    // parameters: original list of local variables, names of target variables 
    private static HashSet<Variable> Get_Target_Variables_Duplicates(List<Variable> locVars, HashSet<string> target_names)
    {
      HashSet<Variable> res = new HashSet<Variable>();

      foreach (string s in target_names) {
        foreach (Variable v in locVars) {
          if (s == v.Name) {
            IToken tok_for_basicType = new Token();
            BasicType b_type;
            if (v.TypedIdent.Type.IsInt)
            {
              b_type = new BasicType(tok_for_basicType, SimpleType.Int);
            }
            else if (v.TypedIdent.Type.IsReal)
            {
              b_type = new BasicType(tok_for_basicType, SimpleType.Real);
            }
            else if (v.TypedIdent.Type.IsBool)
            {
              b_type = new BasicType(tok_for_basicType, SimpleType.Bool);
            }
            else {
              b_type = new BasicType(tok_for_basicType, SimpleType.RMode);
            }

            
            IToken tok_for_typeIdent = new Token();
            string name_duplicate = v.Name + "_duplicate";
            TypedIdent t_Ident = new TypedIdent(tok_for_typeIdent, name_duplicate, b_type);

            IToken tok_for_var = new Token();
            LocalVariable var_duplicate = new LocalVariable(tok_for_var, t_Ident);

            res.Add(var_duplicate);
            break;
          }
        }
      }
      
      return res;
    }
    // end Get_Target_Variables_Duplicates

    // the method extracts all target variables relative to the corresponding loop from a given BigBlock
    // the variables are added to the dictionary according to the id of the loop they were found in
    // if a variable is inside a nested loop, it appears in a dictionary once for each loop id 
    private static void Collect_Target_Names_by_Loop(Dictionary<string, HashSet<string>> targets_by_loop, BigBlock bb)
    {
      // TODO
    }
    // end Collect_Target_Names_by_Loop

    public static HashSet<string> GetTargetNames(BigBlock bb, bool in_loop)
    {
      HashSet<string> res = new HashSet<string>();

      // first we check, what is inside StructuredCmd field
      if (bb.ec != null)
      {
        if (bb.ec is IfCmd)
        {
          IfCmd ec_if = (IfCmd)bb.ec;
          res.UnionWith( GetTargetsFromIf(ec_if, in_loop) );
        }
        else if (bb.ec is WhileCmd)
        {
          WhileCmd ec_while = (WhileCmd)bb.ec;
          res.UnionWith( GetTargetsFromWhile(ec_while) );
        }
      }
      
      // if we are already inside a loop,
      // we have to collect the target variables
      if (in_loop)
      {
        if (bb.simpleCmds.Count > 0)
        {
          foreach (Cmd c in bb.simpleCmds)
          {
            // we care only about assignments and need to the name of variable from the left side 
            if (c is AssignCmd)
            {
              AssignCmd ac = (AssignCmd)c;
              // apparently there can be several left hand sides, so we use Lhss[0]
              // TODO: exception, if more then one left hand side
              string var_name = ac.Lhss[0].DeepAssignedIdentifier.Name;
              res.Add(var_name);
            }
          }
        }
      }

      return res;
    }
    // end GetTargetsNames

    private static HashSet<string> GetTargetsFromWhile(WhileCmd ec_while)
    {
      HashSet<string> res = new HashSet<string>();

      foreach (BigBlock bb in ec_while.Body.BigBlocks)
      {
        res.UnionWith( GetTargetNames(bb, true) );
      } 

      return res;
    }
    // end GetTargetsFromWhile

    public static HashSet<string> GetTargetsFromIf(IfCmd ec_if, bool in_loop) 
    {
      HashSet<string> res = new HashSet<string>();

      // chekc if branch
      if (ec_if.thn != null)
      {
        foreach (BigBlock bb in ec_if.thn.BigBlocks)
        {
          res.UnionWith( GetTargetNames(bb, in_loop) );
        }
      }

      // else if clause is implemented as nested if statements
      if (ec_if.elseIf != null)
      { 
        res.UnionWith( GetTargetsFromIf(ec_if.elseIf, in_loop) );       
      }

      // check else
      if (ec_if.elseBlock != null)
      {
        foreach (BigBlock bb in ec_if.elseBlock.BigBlocks)
        {
          res.UnionWith( GetTargetNames(bb, in_loop) );
        }
      }

      return res;
    }
    // end GetTargetsFromIf

    // the method prints the program text to the console or file
    // it is here for debuging / development purposes only 
    public static void PrintBplFile(string filename, Program program, bool allowPrintDesugaring, bool setTokens = true, bool pretty = false)
    {
      Contract.Requires(program != null);
      Contract.Requires(filename != null);
      bool oldPrintDesugaring = CommandLineOptions.Clo.PrintDesugarings;
      if (!allowPrintDesugaring)
      {
        CommandLineOptions.Clo.PrintDesugarings = false;
      }
      using (TokenTextWriter writer = filename == "-" ?
                                      new TokenTextWriter("<console>", Console.Out, setTokens, pretty) :
                                      new TokenTextWriter(filename, setTokens, pretty))
      {
        if (CommandLineOptions.Clo.ShowEnv != CommandLineOptions.ShowEnvironment.Never)
        {
          writer.WriteLine("// " + CommandLineOptions.Clo.Version);
          writer.WriteLine("// " + CommandLineOptions.Clo.Environment);
        }
        writer.WriteLine();
        program.Emit(writer);
      }
      CommandLineOptions.Clo.PrintDesugarings = oldPrintDesugaring;
    }
    // end PrintBplFile

  }
  // end class Translator

}
// end namespace Core
