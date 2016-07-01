using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace NuBuild
{
    class DafnyExecutableDependencies
    {
        private static SourcePath dafnyExecutable;

        public static SourcePath getDafnyExecutable()
        {
            // TODO this should eventually be a BuildObject from *building* the executable.
            if (dafnyExecutable == null)
            {
                dafnyExecutable = new SourcePath("tools\\Dafny\\Dafny.exe", SourcePath.SourceType.Tools);
            }

            return dafnyExecutable;
        }


        public static IEnumerable<BuildObject> getDafnyExecutableDependencies()
        {
            List<BuildObject> exeDepends = new List<BuildObject>();

            exeDepends.Add(getDafnyExecutable());
            exeDepends.Add(new SourcePath("tools\\Dafny\\AbsInt.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BaseTypes.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieAbsInt.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieBasetypes.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieCodeContractsExtender.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieConcurrency.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieCore.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieDoomed.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieExecutionEngine.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieGraph.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieHoudini.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieModel.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieModelViewer.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieParserHelper.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogiePredication.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieVCExpr.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\BoogieVCGeneration.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\CodeContractsExtender.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Concurrency.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Core.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Dafny.exe.config", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\DafnyPipeline.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\DafnyPrelude.bpl", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Doomed.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\ExecutionEngine.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Graph.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Houdini.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Microsoft.Z3.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Microsoft.Z3V3.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Model.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\ModelViewer.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\msvcp100.dll", SourcePath.SourceType.Tools));  // Needed by z3.
            exeDepends.Add(new SourcePath("tools\\Dafny\\msvcr100.dll", SourcePath.SourceType.Tools));  // Needed by z3.
            exeDepends.Add(new SourcePath("tools\\Dafny\\ParserHelper.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Predication.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\Provers.SMTLib.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\System.Collections.Immutable.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\VCExpr.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\VCGeneration.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\vcomp100.dll", SourcePath.SourceType.Tools));  // Needed by z3.
            exeDepends.Add(new SourcePath("tools\\Dafny\\DafnyRuntime.cs", SourcePath.SourceType.Tools));  // Needed for compilation
            exeDepends.Add(new SourcePath("tools\\Dafny\\z3.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\z3_dbg.dll", SourcePath.SourceType.Tools));
            exeDepends.Add(new SourcePath("tools\\Dafny\\z3.exe", SourcePath.SourceType.Tools));

            return exeDepends;
        }
    }
}
