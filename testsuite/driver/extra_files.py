# Extra files that tests depend on.
# Maybe move this information to .T files at some point.

extra_src_files = {
  '10queens': ['Main.hs'],
  'Capi_Ctype_001': ['Capi_Ctype_A_001.hsc', 'capi_ctype_001.h', 'capi_ctype_001_c.c'],
  'Capi_Ctype_002': ['Capi_Ctype_A_002.hsc', 'capi_ctype_002_A.h', 'capi_ctype_002_B.h'],
  'Defer02': ['../../typecheck/should_run/Defer01.hs'],
  'DeprU': ['DeprM.hs'],
  'ExportSyntaxImport': ['ExportSyntax.hs'],
  'ExtraConstraintsWildcardInTypeSpliceUsed': ['ExtraConstraintsWildcardInTypeSplice.hs'],
  'GFunctor1': ['GFunctor.hs', 'Main.hs'],
  'GMap1': ['GMap.hs', 'Main.hs'],
  'GShow1': ['GShow.hs', 'Main.hs'],
  'GUniplate1': ['GUniplate.hs', 'Main.hs'],
  'ImpExp_Imp': ['ImpExp_Exp.hs'],
  'ImpSafeOnly01': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'ImpSafeOnly02': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'ImpSafeOnly03': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'ImpSafeOnly04': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'ImpSafeOnly05': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'ImpSafeOnly06': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'ImpSafeOnly07': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'ImpSafeOnly08': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'ImpSafeOnly09': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'ImpSafeOnly10': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'SplicesUsed': ['Splices.hs'],
  'T10138': ['.keepme.hpc.T10138/'],
  'T10255': ['Test10255.hs'],
  'T10268': ['Test10268.hs'],
  'T10269': ['Test10269.hs'],
  'T10276': ['Test10276.hs'],
  'T10278': ['Test10278.hs'],
  'T10280': ['Test10280.hs'],
  'T10294': ['annotation-plugin/'],
  'T10294a': ['annotation-plugin/'],
  'T10307': ['Test10307.hs'],
  'T10309': ['Test10309.hs'],
  'T10312': ['Test10312.hs'],
  'T10313': ['Test10313.hs', 'stringSource.hs'],
  'T10354': ['Test10354.hs'],
  'T10357': ['Test10357.hs'],
  'T10358': ['Test10358.hs'],
  'T10396': ['Test10396.hs'],
  'T10399': ['Test10399.hs'],
  'T12417': ['Test12417.hs'],
  'T13163': ['Test13163.hs'],
  'T10420': ['rule-defining-plugin/'],
  'T10458': ['A.c'],
  'T10598':  ['Test10598.hs'],
  'T10637': ['A.hs', 'A.hs-boot'],
  'T10672_x64': ['Main.hs', 'Printf.hs', 'cxxy.cpp'],
  'T10672_x86': ['Main.hs', 'Printf.hs', 'cxxy.cpp'],
  'T10890': ['A.hs', 'B.hs'],
  'T10890_1': ['Base.hs', 'Extends.hs'],
  'T10955': ['A.c', 'B.c'],
  'T10955dyn': ['A.c', 'B.c'],
  'T10971d': ['T10971c.hs'],
  'T11018': ['Test11018.hs'],
  'T11062': ['T11062.hs','T11062.hs-boot','T11062a.hs'],
  'T11072gcc': ['A.c', 'T11072.hs'],
  'T11072msvc': ['A.c', 'T11072.hs', 'libAS.def', 'i686/', 'x86_64/'],
  'T11223_link_order_a_b_2_fail': ['bar.c', 'foo.c', 'foo3.hs'],
  'T11223_link_order_a_b_succeed': ['bar.c', 'foo.c', 'foo2.hs'],
  'T11223_link_order_b_a_2_succeed': ['bar.c', 'foo.c', 'foo3.hs'],
  'T11223_link_order_b_a_succeed': ['bar.c', 'foo.c', 'foo2.hs'],
  'T11223_simple_duplicate': ['bar.c', 'foo.c', 'foo.hs'],
  'T11223_simple_duplicate_lib': ['bar.c', 'foo.c', 'foo.hs'],
  'T11223_simple_link': ['foo.c', 'foo.hs'],
  'T11223_simple_link_lib': ['foo.c', 'foo.hs'],
  'T11223_simple_unused_duplicate_lib': ['bar.c', 'foo.c', 'foo.hs'],
  'T11223_weak_both_link_order_a_b_succeed': ['power.c', 'power3.hs', 'power_slow.c'],
  'T11223_weak_both_link_order_b_a_succeed': ['power.c', 'power3.hs', 'power_slow.c'],
  'T11223_weak_only_link_fail': ['power.c', 'power.hs'],
  'T11223_weak_only_link_succeed': ['power3.hs', 'power_slow.c'],
  'T11223_weak_single_link_order_a_b_succeed': ['power.c', 'power3.hs', 'power_slow.c'],
  'T11223_weak_single_link_order_b_a_succeed': ['power.c', 'power3.hs', 'power_slow.c'],
  'T11244': ['rule-defining-plugin/'],
  'T11321': ['Test11321.hs'],
  'T11332': ['Test11332.hs'],
  'T11430': ['Test11430.hs', 't11430.hs'],
  'T11827': ['A.hs', 'A.hs-boot', 'B.hs'],
  'T12062': ['A.hs', 'A.hs-boot', 'C.hs'],
  'T12035j': ['T12035.hs', 'T12035a.hs', 'T12035.hs-boot'],
  'T12042': ['T12042.hs', 'T12042a.hs', 'T12042.hs-boot'],
  'T12485': ['a.pkg', 'b.pkg', 'Main.hs'],
  'T12485a': ['shadow1.pkg', 'shadow2.pkg', 'shadow3.pkg'],
  'T12733': ['p/', 'q/', 'Setup.hs'],
  'T1372': ['p1/', 'p2/'],
  'T1407': ['A.c'],
  'T1959': ['B.hs', 'C.hs', 'D.hs', 'E1.hs', 'E2.hs'],
  'T2014': ['A.hs', 'A.hs-boot', 'B.hs', 'C.hs'],
  'T2615': ['libfoo_T2615.c', 'libfoo_script_T2615.so'],
  'T3007': ['A/', 'B/'],
  'T3103': ['Foreign/', 'GHC/'],
  'T4198': ['exitminus1.c'],
  'T437': ['Test.hs', 'Test2.hs'],
  'T4491': ['A.hs'],
  'T4891': ['X.hs'],
  'T5147': ['A.hs', 'B1.hs', 'B2.hs'],
  'T5250': ['spalign.c'],
  'T5435_dyn_gcc': ['T5435.hs', 'T5435_gcc.c'],
  'T5442a': ['test.pkg'],
  'T5442b': ['test.pkg'],
  'T5442c': ['test.pkg'],
  'T5442d': ['shadow1.pkg', 'shadow2.pkg', 'shadow4.pkg'],
  'T5644': ['Conf.hs', 'ManyQueue.hs', 'Util.hs', 'heap-overflow.hs'],
  'T6018fail': ['T6018Afail.hs', 'T6018Bfail.hs', 'T6018Cfail.hs', 'T6018Dfail.hs'],
  'T6106': ['../shell.hs'],
  'T7040_ghci': ['T7040_c.h'],
  'T7354a': ['T7354b.hs'],
  'T7373': ['D.hs', 'pkg/'],
  'T7478': ['A.hs', 'B.hs', 'C.hs'],
  'T7702': ['T7702plugin'],
  'T7835': ['Test.hs', 'TestPrim.hs', 'test-prims.cmm'],
  'T8184': ['A.hs', 'B.hs', 'B.hs-boot', 'C.hs'],
  'T8353': ['Defer03.hs'],
  'T8425': ['Arr.hs', 'Base.hs', 'BuggyOpt.hs', 'Good.hs', 'M.hs', 'Main.hs'],
  'T8526': ['A.hs'],
  'T8602': ['A.hs'],
  'T9293': ['ghci057.hs'],
  'T9562': ['A.hs', 'B.hs', 'B.hs-boot', 'C.hs', 'D.hs', 'Main.hs'],
  'T9619': ['.hpc', '.hpc.copy', 'hpc_sample.tix'],
  'T9646': ['Main.hs', 'Natural.hs', 'StrictPrim.hs', 'Type.hs'],
  'TH_import_loop': ['Main.hs', 'ModuleA.hs', 'ModuleA.hs-boot', 'ModuleB.hs', 'ModuleC.hs'],
  'TH_spliceViewPat': ['A.hs', 'Main.hs'],
  'andre_monad': ['Main.hs'],
  'andy_cherry': ['DataTypes.hs', 'GenUtils.hs', 'Interp.hs', 'InterpUtils.hs', 'Main.hs', 'Parser.hs', 'PrintTEX.hs', 'mygames.pgn'],
  'annfail04': ['Annfail04_Help.hs'],
  'annfail05': ['Annfail05_Help.hs'],
  'annfail06': ['Annfail06_Help.hs'],
  'annotations': ['AnnotationLet.hs'],
  'annrun01': ['Annrun01_Help.hs'],
  'annth_compunits': ['AnnHelper.hs', 'TestModule.hs', 'TestModuleTH.hs', 'annth.hs'],
  'annth_make': ['AnnHelper.hs', 'TestModule.hs', 'TestModuleTH.hs', 'annth.hs'],
  'apirecomp001': ['A.hs', 'B.hs', 'myghc.hs'],
  'barton-mangler-bug': ['Basic.hs', 'Expected.hs', 'Main.hs', 'Physical.hs', 'Plot.lhs', 'PlotExample.lhs', 'TypesettingTricks.hs'],
  'base01': ['GHC'],
  'boolFormula': ['TestBoolFormula.hs'],
  'bkpcabal01': ['p', 'q', 'impl', 'bkpcabal01.cabal', 'Setup.hs', 'Main.hs'],
  'bkpcabal02': ['p', 'q', 'bkpcabal02.cabal', 'Setup.hs'],
  'bkpcabal03': ['asig1', 'asig2', 'bkpcabal03.cabal.in1', 'bkpcabal03.cabal.in2', 'Setup.hs', 'Mod.hs'],
  'bkpcabal04': ['p','q','bkpcabal04.cabal.in1','bkpcabal04.cabal.in2','Setup.hs'],
  'bkpcabal05': ['bkpcabal05.cabal','A.hsig.in1','A.hsig.in2','M.hs','Setup.hs'],
  'break001': ['../Test2.hs'],
  'break002': ['../Test2.hs'],
  'break003': ['../Test3.hs'],
  'break005': ['../QSort.hs'],
  'break006': ['../Test3.hs'],
  'break007': ['Break007.hs'],
  'break008': ['../Test3.hs'],
  'break009': ['../Test6.hs'],
  'break010': ['../Test6.hs'],
  'break011': ['../Test7.hs'],
  'break017': ['../QSort.hs'],
  'break018': ['../mdo.hs'],
  'break019': ['../Test2.hs'],
  'break020': ['Break020b.hs'],
  'break021': ['Break020b.hs', 'break020.hs'],
  'break022': ['A1.hs', 'B.hs', 'B.hs-boot', 'C.hs'],
  'break023': ['A1.hs', 'B.hs', 'B.hs-boot', 'C.hs'],
  'break027': ['../QSort.hs'],
  'bug1465': ['B1.hs', 'B2.hs', 'C.hs', 'v1/', 'v2/'],
  'bug1677': ['Bar.hs', 'Foo.hs'],
  'bundle-export': ['BundleExport.hs'],
  'cabal03': ['Setup.lhs', 'p/', 'q/', 'r/'],
  'cabal04': ['Library.hs', 'Setup.lhs', 'TH.hs', 'thtest.cabal'],
  'cabal05': ['Setup.hs', 'p/', 'q/', 'r/', 's/', 't/'],
  'cabal06': ['Setup.hs', 'p-1.0/', 'p-1.1/', 'q/', 'r/'],
  'cabal08': ['Main.hs', 'Setup.hs', 'p1/', 'p2/'],
  'cabal09': ['Main.hs', 'Setup.hs', 'reexport.cabal'],
  'ccfail004': ['Ccfail004A.hs'],
  'cgrun067': ['Cgrun067A.hs'],
  'cholewo-eval': ['Arr.lhs', 'Main.lhs'],
  'comments': ['CommentsTest.hs'],
  'concio001.thr': ['concio001.hs'],
  'concprog001': ['Arithmetic.hs', 'Converter.hs', 'Mult.hs', 'Stream.hs', 'Thread.hs', 'Trit.hs', 'Utilities.hs'],
  'concprog002': ['Event.hs', 'Scheduler.hs', 'Server.hs', 'Thread.hs'],
  'concprog003': ['CASList.hs', 'Collection.hs', 'IOList.lhs', 'ImmList.hs', 'MVarListLockCoupling.hs', 'Main.lhs', 'RefInterface.hs', 'TestData.hs', 'TestDataParser.hs', 'TestRun.hs', 'test-8-3000-3000-2-1-4'],
  'cvh_unboxing': ['Append.lhs', 'Main.lhs', 'Types.lhs'],
  'determ002': ['A.hs'],
  'determ003': ['A.hs'],
  'determ005': ['A.hs'],
  'determ006': ['spec-inline-determ.hs'],
  'determ007': ['A.hs'],
  'determ008': ['A.hs'],
  'determ009': ['A.hs'],
  'determ010': ['A.hs'],
  'determ011': ['A.hs'],
  'determ012': ['A.hs'],
  'determ013': ['A.hs'],
  'determ014': ['A.hs'],
  'determ015': ['A.hs'],
  'determ016': ['A.hs'],
  'determ017': ['A.hs'],
  'determ018': ['A.hs'],
  'determ019': ['A.hs'],
  'determ021': ['A.hs'],
  'dodgy': ['DodgyA.hs'],
  'driver011': ['A011.hs'],
  'driver012': ['A012.hs'],
  'driver013': ['A013.hs'],
  'driver014': ['A014.hs'],
  'driver015': ['A015.hs'],
  'driver016': ['F016.hs'],
  'driver017': ['F017.hs'],
  'driver018': ['F018.hs'],
  'driver018a': ['F018a.hs'],
  'driver019': ['F019.hs'],
  'driver021': ['B021/'],
  'driver022': ['B022/'],
  'driver023': ['B023/'],
  'driver024': ['B024/'],
  'driver025': ['B025/'],
  'driver026': ['d026/'],
  'driver027': ['B027/'],
  'driver028': ['B028/'],
  'driver031': ['A031.hs'],
  'driver032': ['A032.hs'],
  'driver033': ['A033.hs'],
  'driver034': ['F034.hs'],
  'driver035': ['F035.hs'],
  'driver041': ['B041/'],
  'driver042': ['B042/'],
  'driver042stub': ['B042stub/'],
  'driver043': ['B043/'],
  'driver044': ['B044/'],
  'driver045': ['B045/'],
  'driver051': ['d051_1/', 'd051_2/'],
  'driver052': ['d052_1/', 'd052_2/'],
  'driver053': ['d053_1/', 'd053_2/'],
  'driver061a': ['A061a.hs'],
  'driver061b': ['A061b.hs'],
  'driver063': ['D063.hs'],
  'driver064': ['A064.hs'],
  'driver065': ['A065.hs'],
  'driver066': ['A066.hs'],
  'driver067': ['A067.hs'],
  'driver070': ['A070.hs'],
  'driver071': ['A071.hs'],
  'driver100': ['overlap/'],
  'driver200': ['A200.hs', 'B200/', 'D200.hs'],
  'dynamicToo001': ['A.hs', 'B.hs', 'B1.hs', 'B2.hs', 'C.hs'],
  'dynamicToo002': ['A.hs', 'B.hs', 'C.hs'],
  'dynamicToo003': ['A003.hs'],
  'dynamicToo004': ['Setup.hs', 'pkg1/', 'pkg1dyn/', 'pkg2/', 'prog.hs'],
  'dynamicToo005': ['dynamicToo005.bkp'],
  'dynamic_flags_001': ['A.hs', 'B.hs', 'C.hs'],
  'dynbrk001': ['../QSort.hs'],
  'dynbrk002': ['../QSort.hs'],
  'dynbrk004': ['../mdo.hs'],
  'encoding004': ['encoded-data/'],
  'enum01': ['enum_processor.bat', 'enum_processor.py'],
  'enum02': ['enum_processor.bat', 'enum_processor.py'],
  'enum03': ['enum_processor.bat', 'enum_processor.py'],
  'exampleTest': ['AnnotationTuple.hs'],
  'fast2haskell': ['Fast2haskell.hs', 'Main.hs'],
  'ffi018_ghci': ['ffi018.h'],
  'frontend01': ['FrontendPlugin.hs'],
  'fun_insts': ['Main.hs'],
  'gadt17': ['Gadt17_help.hs'],
  'gadt23': ['Gadt23_AST.hs'],
  'galois_raytrace': ['CSG.hs', 'Construct.hs', 'Data.hs', 'Eval.hs', 'Geometry.hs', 'Illumination.hs', 'Intersections.hs', 'Interval.hs', 'Main.hs', 'Misc.hs', 'Parse.hs', 'Primitives.hs', 'Surface.hs', 'galois.gml'],
  'getargs': ['../getargs.hs'],
  'ghci.prog007': ['A.hs', 'B.hs', 'C.hs', 'C.hs-boot'],
  'ghci.prog008': ['A.hs'],
  'ghci.prog009': ['A1.hs', 'A2.hs', 'A3.hs', 'B.hs'],
  'ghci025': ['Ghci025B.hs', 'Ghci025C.hs', 'Ghci025D.hs'],
  'ghci026': ['../prog002'],
  'ghci038': ['../shell.hs'],
  'ghci058': ['../shell.hs'],
  'ghcilink001': ['TestLink.hs', 'f.c'],
  'ghcilink002': ['TestLink.hs', 'f.c'],
  'ghcilink004': ['TestLink.hs', 'f.c'],
  'ghcilink005': ['TestLink.hs', 'f.c'],
  'ghcpkg01': ['test.pkg', 'test2.pkg', 'test3.pkg'],
  'ghcpkg03': ['test.pkg', 'test2.pkg', 'test4.pkg'],
  'ghcpkg04': ['test.pkg', 'test5.pkg'],
  'ghcpkg05': ['test2.pkg', 'test3.pkg'],
  'ghcpkg06': ['test.pkg', 'testdup.pkg'],
  'ghcpkg07': ['test.pkg', 'test7a.pkg', 'test7b.pkg'],
  'haddock.Cabal': ['../../../../libraries/Cabal/Cabal/dist-install/haddock.t'],
  'haddock.Test': ['Hidden.hs', 'Test.hs', 'Visible.hs'],
  'haddock.base': ['../../../../libraries/base/dist-install/haddock.t'],
  'haddock.compiler': ['../../../../compiler/stage2/haddock.t'],
  'heapprof002': ['heapprof001.hs'],
  'hist001': ['../Test3.hs'],
  'hpc_draft': ['.hpc/', 'hpc001.hs', 'hpc_sample.tix'],
  'hpc_fork': ['../hpcrun.pl'],
  'hpc_ghc_ghci': ['A.hs', 'B.hs'],
  'hpc_hand_overlay': ['.hpc/', 'hand_overlay.ovr', 'hpc001.hs', 'hpc_sample.tix'],
  'hpc_markup_001': ['.hpc/', 'hpc001.hs', 'hpc_sample.tix'],
  'hpc_markup_002': ['.hpc/', 'hpc001.hs', 'hpc_sample.tix'],
  'hpc_markup_multi_001': ['../Geometry.hs', '.hpc/', 'hpc_sample.tix'],
  'hpc_markup_multi_002': ['../CSG.hs', '../Construct.hs', '../Data.hs', '../Eval.hs', '../Geometry.hs', '../Illumination.hs', '../Intersections.hs', '../Interval.hs', '../Main.hs', '../Misc.hs', '../Parse.hs', '../Pixmap.hs', '../Primitives.hs', '../RayTrace.hs', '../Surface.hs', '.hpc/', 'hpc_sample.tix'],
  'hpc_markup_multi_003': ['../CSG.hs', '../Construct.hs', '../Data.hs', '../Eval.hs', '../Geometry.hs', '../Illumination.hs', '../Intersections.hs', '../Interval.hs', '../Main.hs', '../Misc.hs', '../Parse.hs', '../Pixmap.hs', '../Primitives.hs', '../RayTrace.hs', '../Surface.hs', '.hpc/', 'hpc_sample.tix'],
  'hpc_overlay': ['.hpc/', 'hpc001.hs', 'hpc_sample.tix', 'sample_overlay.ovr'],
  'hpc_overlay2': ['.hpc/', 'hpc001.hs', 'hpc_sample.tix', 'sample_overlay.ovr'],
  'hpc_raytrace': ['../hpcrun.pl', 'CSG.hs', 'Construct.hs', 'Data.hs', 'Eval.hs', 'Geometry.hs', 'Illumination.hs', 'Intersections.hs', 'Interval.hs', 'Main.hs', 'Misc.hs', 'Parse.hs', 'Primitives.hs', 'Surface.hs', 'galois.gml', 'galois.sample'],
  'hpc_report_001': ['.hpc/', 'hpc_sample.tix'],
  'hpc_report_002': ['.hpc/', 'hpc_sample.tix'],
  'hpc_report_003': ['.hpc/', 'hpc_sample.tix'],
  'hpc_report_multi_001': ['.hpc/', 'hpc_sample.tix'],
  'hpc_report_multi_002': ['.hpc/', 'hpc_sample.tix'],
  'hpc_report_multi_003': ['.hpc/', 'hpc_sample.tix'],
  'hpc_show': ['.hpc', 'hpc_sample.tix'],
  'hpc_show_multi_001': ['.hpc/', 'hpc_sample.tix'],
  'hpc_show_multi_002': ['.hpc/', 'hpc_sample.tix'],
  'hs-boot': ['A.hs', 'A.hs-boot', 'B.hs', 'C.hs', 'Main.hs'],
  'impexp': ['Exp.hs', 'Imp.hs'],
  'ind2': ['Ind2_help.hs'],
  'jl_defaults': ['Main.hs'],
  'joao-circular': ['Data_Lazy.hs', 'Funcs_Lexer.hs', 'Funcs_Parser_Lazy.hs', 'LrcPrelude.hs', 'Main.hs', 'Visfun_Lazy.hs', 'inp'],
  'jq_readsPrec': ['Main.hs'],
  'jtod_circint': ['Bit.hs', 'LogFun.hs', 'Main.hs', 'Signal.hs'],
  'jules_xref': ['Main.hs'],
  'jules_xref2': ['Main.hs'],
  'launchbury': ['Main.hs'],
  'lazy-bs-alloc': ['../../numeric/should_run/arith011.stdout'],
  'lennart_range': ['Main.hs'],
  'lex': ['Main.hs'],
  'life_space_leak': ['Main.hs'],
  'linker_error1': ['linker_error.c'],
  'linker_error2': ['linker_error.c'],
  'linker_error3': ['linker_error.c'],
  'linker_unload': ['LinkerUnload.hs', 'Test.hs'],
  'listCommand001': ['../Test3.hs'],
  'listcomps': ['ListComprehensions.hs'],
  'literals': ['LiteralsTest.hs'],
  'load_short_name': ['A.c'],
  'maessen_hashtab': ['Data/', 'HashTest.hs'],
  'memo001': ['Memo1.lhs'],
  'memo002': ['Memo2.lhs'],
  'mod101': ['Mod101_AuxA.hs', 'Mod101_AuxB.hs'],
  'mod102': ['Mod102_AuxA.hs', 'Mod102_AuxB.hs'],
  'mod114': ['Mod114_Help.hs'],
  'mod115': ['Mod115_A.hs', 'Mod115_B.hs'],
  'mod117': ['Mod117_A.hs', 'Mod117_B.hs'],
  'mod118': ['Mod118_A.hs', 'Mod118_B.hs'],
  'mod119': ['Mod119_A.hs', 'Mod119_B.hs'],
  'mod120': ['Mod120_A.hs'],
  'mod121': ['Mod121_A.hs'],
  'mod122': ['Mod122_A.hs'],
  'mod123': ['Mod123_A.hs'],
  'mod124': ['Mod124_A.hs'],
  'mod125': ['Mod125_A.hs'],
  'mod126': ['Mod126_A.hs'],
  'mod127': ['Mod127_A.hs'],
  'mod128': ['Mod128_A.hs'],
  'mod131': ['Mod131_A.hs', 'Mod131_B.hs'],
  'mod132': ['Mod132_A.hs', 'Mod132_B.hs'],
  'mod136': ['Mod136_A.hs'],
  'mod137': ['Mod137_A.hs'],
  'mod138': ['Mod138_A.hs'],
  'mod139': ['Mod139_A.hs', 'Mod139_B.hs'],
  'mod140': ['Mod140_A.hs'],
  'mod141': ['Mod141_A.hs'],
  'mod142': ['Mod142_A.hs'],
  'mod143': ['Mod143_A.hs'],
  'mod144': ['Mod144_A.hs'],
  'mod145': ['Mod145_A.hs'],
  'mod146': ['Mod145_A.hs'],
  'mod147': ['Mod147_A.hs'],
  'mod157': ['Mod157_A.hs', 'Mod157_B.hs', 'Mod157_C.hs', 'Mod157_D.hs'],
  'mod158': ['Mod157_A.hs', 'Mod157_B.hs', 'Mod157_C.hs', 'Mod157_D.hs'],
  'mod159': ['Mod159_A.hs', 'Mod159_B.hs', 'Mod159_C.hs', 'Mod159_D.hs'],
  'mod160': ['Mod159_A.hs', 'Mod159_B.hs', 'Mod159_C.hs', 'Mod159_D.hs'],
  'mod162': ['Mod162_A.hs'],
  'mod163': ['Mod163_A.hs'],
  'mod164': ['Mod164_A.hs', 'Mod164_B.hs'],
  'mod165': ['Mod164_A.hs', 'Mod164_B.hs'],
  'mod166': ['Mod164_A.hs', 'Mod164_B.hs'],
  'mod167': ['Mod164_A.hs', 'Mod164_B.hs'],
  'mod170': ['Mod170_A.hs'],
  'mod171': ['Mod171_A.hs', 'Mod171_B.hs'],
  'mod172': ['Mod172_B.hs', 'Mod172_C.hs'],
  'mod173': ['Mod173_Aux.hs'],
  'mod175': ['Test.hs', 'Test2.hs'],
  'mod178': ['Mod178_2.hs'],
  'mod179': ['Mod179_A.hs'],
  'mod180': ['Mod180_A.hs', 'Mod180_B.hs'],
  'north_array': ['Main.hs'],
  'okeefe_neural': ['Main.hs'],
  'overloadedlabelsrun04': ['OverloadedLabelsRun04_A.hs'],
  'overloadedrecfldsfail04': ['OverloadedRecFldsFail04_A.hs'],
  'overloadedrecfldsfail06': ['OverloadedRecFldsFail06_A.hs'],
  'overloadedrecfldsfail10': ['OverloadedRecFldsFail10_A.hs', 'OverloadedRecFldsFail10_B.hs', 'OverloadedRecFldsFail10_C.hs'],
  'overloadedrecfldsfail11': ['OverloadedRecFldsFail11_A.hs'],
  'overloadedrecfldsfail12': ['OverloadedRecFldsFail12_A.hs'],
  'overloadedrecfldsrun02': ['OverloadedRecFldsRun02_A.hs'],
  'p10': ['D.hs'],
  'p11': ['E.hs'],
  'p13': ['P13_A.hs'],
  'p7': ['A.hs'],
  'p8': ['B.hs'],
  'p9': ['C.hs'],
  'parseTree': ['AnnotationTuple.hs'],
  'parsed': ['LiteralsTest2.hs'],
  'parser.prog001': ['Read006.hs', 'Read007.hs'],
  'pat-syn-bundle': ['Bundle1.hs', 'BundleInternal1.hs'],
  'pat-syn-trans-bundle': ['Bundle.hs', 'BundleInternal.hs', 'TransBundle.hs'],
  'path_with_commas': ['test.pkg', 'Main.hs', 'Dummy.hs'],
  'pkg02': ['A.hs', 'Foreign.hs'],
  'plugins01': ['simple-plugin/'],
  'plugins02': ['simple-plugin/'],
  'plugins03': ['simple-plugin/'],
  'plugins04': ['HomePackagePlugin.hs'],
  'plugins05': ['HomePackagePlugin.hs'],
  'plugins06': ['LinkerTicklingPlugin.hs'],
  'plugins07': ['rule-defining-plugin/'],
  'T12567a': ['T12567b.hs', 'simple-plugin/'],
  'print002': ['../Test.hs'],
  'print003': ['../Test.hs'],
  'print005': ['../QSort.hs'],
  'print006': ['../Test.hs'],
  'print007': ['../Test.hs'],
  'print008': ['../Test.hs'],
  'print010': ['../Test.hs'],
  'print011': ['../Test.hs'],
  'print012': ['../GADT.hs', '../Test.hs'],
  'print013': ['../GADT.hs'],
  'print014': ['../GADT.hs'],
  'print016': ['../Test.hs'],
  'print017': ['../Test.hs'],
  'print018': ['../Test.hs'],
  'print019': ['../Test.hs'],
  'print020': ['../HappyTest.hs'],
  'print023': ['../Test.hs'],
  'print024': ['../Test.hs'],
  'print030': ['print029.hs'],
  'print032': ['print029.hs'],
  'print034': ['../GADT.hs', '../Test.hs'],
  'print035': ['../Unboxed.hs'],
  'prog001': ['../shell.hs', 'A.hs', 'B.hs', 'C1.hs', 'D1.hs', 'D2.hs'],
  'prog002': ['../shell.hs', 'A1.hs', 'A2.hs', 'B.hs', 'C.hs', 'D.hs'],
  'prog003': ['../shell.hs', 'A.hs', 'B.hs', 'C.hs', 'D1.hs', 'D2.hs'],
  'prog005': ['A1.hs', 'B.hs'],
  'prog006': ['A.hs', 'Boot.hs-boot', 'Boot1.hs', 'Boot2.hs'],
  'prog012': ['../shell.hs', 'Bar1.hs', 'Bar2.hs', 'Foo.hs', 'FooBar.hs'],
  'prog013': ['Bad.hs', 'Good.hs'],
  'prog014': ['Primop.hs', 'dummy.c'],
  'prog015': ['Level1.hs', 'Level2/', 'TopLevel.hs'],
  'prog016': ['Level1.hs', 'Level2/', 'TopLevel.hs'],
  'prog017': ['Level1.hs', 'Level2/', 'TopLevel.hs'],
  'qq005': ['Expr.hs', 'Main.hs'],
  'qq006': ['Expr.hs', 'Main.hs'],
  'qq007': ['QQ.hs', 'Test.hs'],
  'qq008': ['QQ.hs', 'Test.hs'],
  'qq009': ['QQ.hs', 'Test.hs'],
  'recomp001': ['A.hs', 'B1.hs', 'B2.hs', 'C.hs'],
  'recomp002': ['Q.hs', 'W.hs', 'W.hs-boot'],
  'recomp003': ['A.hs'],
  'recomp004': ['Main.hs', 'c.h', 'c1.c', 'c2.c'],
  'recomp005': ['A.hs', 'B.hs', 'C1.hs', 'C2.hs', 'D.hs', 'E.hs'],
  'recomp006': ['A.hs', 'B1.hs', 'B2.hs'],
  'recomp007': ['Setup.hs', 'a1/', 'a2/', 'b/'],
  'recomp008': ['A1.hs', 'A2.hs', 'B.hs', 'Main.hs'],
  'recomp009': ['Main.hs', 'Sub1.hs', 'Sub2.hs'],
  'recomp010': ['Main.hs', 'X1.hs', 'X2.hs'],
  'recomp011': ['Main.hs'],
  'recomp015': ['Generate.hs'],
  'recomp016': ['A.hs', 'A2.hs', 'C.hs', 'D.hs', 'E.hs'],
  'record_upd': ['Main.hs'],
  'rename.prog001': ['Rn037Help.hs', 'rn037.hs'],
  'rename.prog002': ['Rn037Help.hs', 'rnfail037.hs'],
  'rename.prog003': ['A.hs', 'B.hs'],
  'rename.prog004': ['A.hs', 'B.hs', 'C.hs'],
  'rename.prog005': ['VersionGraphClient.hs', 'VersionGraphClient.hs-boot', 'View.hs', 'ViewType.hs'],
  'retc001': ['A.hs', 'B1.hs', 'B2.hs', 'C.hs'],
  'retc002': ['Q.hs', 'W.hs', 'W.hs-boot'],
  'retc003': ['A.hs'],
  'rittri': ['Main.hs'],
  'rn.prog006': ['A.hs', 'B/', 'Main.hs', 'pwd.hs'],
  'rn009': ['Imp10Aux.hs', 'Imp10Aux.hs-boot'],
  'rn011': ['Imp100Aux.hs', 'Imp100Aux.hs-boot'],
  'rn012': ['Imp500Aux.hs', 'Imp500Aux.hs-boot'],
  'rn017': ['RnAux017.hs', 'RnAux017.hs-boot'],
  'rn042': ['Rn042_A.hs'],
  'rn043': ['Rn043_A.hs', 'Rn043_B.hs'],
  'rn044': ['Rn044_A.hs', 'Rn044_B.hs'],
  'rn050': ['Rn050_A.hs'],
  'rn052': ['Rn052Aux.hs'],
  'rn053': ['Rn053_A.hs', 'Rn053_B.hs'],
  'rn059': ['Rn059_A.hs', 'Rn059_B.hs'],
  'rn065': ['Rn065A.hs'],
  'rn066': ['Rn066_A.hs'],
  'rn067': ['Rn067_A.hs'],
  'rnfail040': ['Rnfail040_A.hs'],
  'rnfail047': ['RnFail047_A.hs', 'RnFail047_A.hs-boot'],
  'rnfail055': ['RnFail055.hs', 'RnFail055.hs-boot', 'RnFail055_aux.hs'],
  'rtsopts001': ['rtsOpts.hs'],
  'safePkg01': ['M_SafePkg.hs', 'M_SafePkg2.hs', 'M_SafePkg3.hs', 'M_SafePkg4.hs', 'M_SafePkg5.hs', 'M_SafePkg6.hs', 'M_SafePkg7.hs', 'M_SafePkg8.hs', 'Setup.hs', 'p.cabal'],
  'sanders_array': ['Main.hs'],
  'seward-space-leak': ['Main.lhs'],
  'shared001': ['Shared001.hs'],
  'simpl020': ['Simpl020_A.hs'],
  'simpl021': ['Simpl021A.hs', 'Simpl021B.hs'],
  'simplCore.oneShot': ['OneShot1.hs', 'OneShot2.hs'],
  'simplCore.prog001': ['Simpl006Help.hs', 'simpl006.hs'],
  'simplCore.prog002': ['Simpl009Help.hs', 'simpl009.hs'],
  'static001': ['Static001.hs'],
  'strict_anns': ['Main.hs'],
  'tc170': ['Tc170_Aux.hs'],
  'tc173': ['Tc173a.hs', 'Tc173b.hs'],
  'tc239': ['Tc239_Help.hs'],
  'tc245': ['Tc245_A.hs'],
  'tc251': ['Tc251_Help.hs'],
  'tc263': ['Tc263_Help.hs'],
  'tc266': ['Tc266.hs', 'Tc266a.hs', 'Tc266.hs-boot'],
  'Tc267': ['Tc267a.hs', 'Tc267b.hs', 'Tc267a.hs-boot', 'Tc267b.hs-boot'],
  'tcfail186': ['Tcfail186_Help.hs'],
  'tcrun025': ['TcRun025_B.hs'],
  'tcrun038': ['TcRun038_B.hs'],
  'testwsdeque': ['../../../rts/WSDeque.h'],
  'thurston-modular-arith': ['Main.hs', 'TypeVal.hs'],
  'tough': ['../hpcrun.pl'],
  'tough2': ['../hpcrun.pl', 'subdir/'],
  'typecheck.prog001': ['A.hs', 'B.hs', 'C.hs'],
  'typecheck.prog002': ['A.hs', 'B.hs'],
  'typecheck.testeq1': ['FakePrelude.hs', 'Main.hs', 'TypeCast.hs', 'TypeEq.hs'],
  'write_interface_make': ['A011.hs'],
  'write_interface_oneshot': ['A011.hs'],
}
