test('qq008',
     [when(fast(), skip),
      extra_clean(['QQ.hi', 'QQ.o', 'Test.hi', 'Test.o']),
      pre_cmd('$MAKE -s --no-print-directory TH_QQ'),
      ],
     multimod_compile,
     ['Test', '-v0 ' + config.ghc_th_way_flags])
