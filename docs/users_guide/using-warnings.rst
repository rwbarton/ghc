.. _options-sanity:

Warnings and sanity-checking
----------------------------

.. index::
   single: sanity-checking options
   single: warnings

GHC has a number of options that select which types of non-fatal error
messages, otherwise known as warnings, can be generated during
compilation. By default, you get a standard set of warnings which are
generally likely to indicate bugs in your program. These are:

.. hlist::
    :columns: 3

    * :ghc-flag:`-Woverlapping-patterns`
    * :ghc-flag:`-Wwarnings-deprecations`
    * :ghc-flag:`-Wdeprecated-flags`
    * :ghc-flag:`-Wunrecognised-pragmas`
    * :ghc-flag:`-Wmissed-specialisations`
    * :ghc-flag:`-Wduplicate-constraints`
    * :ghc-flag:`-Wduplicate-exports`
    * :ghc-flag:`-Woverflowed-literals`
    * :ghc-flag:`-Wempty-enumerations`
    * :ghc-flag:`-Wmissing-fields`
    * :ghc-flag:`-Wmissing-methods`
    * :ghc-flag:`-Wwrong-do-bind`
    * :ghc-flag:`-Wunsupported-calling-conventions`
    * :ghc-flag:`-Wdodgy-foreign-imports`
    * :ghc-flag:`-Winline-rule-shadowing`
    * :ghc-flag:`-Wunsupported-llvm-version`
    * :ghc-flag:`-Wtabs`

The following flags are simple ways to select standard "packages" of warnings:

.. ghc-flag:: -W

    Provides the standard warnings plus :ghc-flag:`-Wunused-binds`,
    :ghc-flag:`-Wunused-matches`, :ghc-flag:`-Wunused-imports`,
    :ghc-flag:`-Wincomplete-patterns`, :ghc-flag:`-Wdodgy-exports`, and
    :ghc-flag:`-Wdodgy-imports`.

.. ghc-flag:: -Wall

    Turns on all warning options that indicate potentially suspicious
    code. The warnings that are *not* enabled by :ghc-flag:`-Wall` are
    :ghc-flag:`-Wincomplete-uni-patterns`,
    :ghc-flag:`-Wincomplete-record-updates`,
    :ghc-flag:`-Wmonomorphism-restriction`,
    :ghc-flag:`-Wimplicit-prelude`, :ghc-flag:`-Wmissing-local-sigs`,
    :ghc-flag:`-Wmissing-exported-sigs`, :ghc-flag:`-Wmissing-import-lists`
    and :ghc-flag:`-Widentities`.

.. ghc-flag:: -Wcompat

    Turns on warnings that will be enabled by default in the future, but remain
    off in normal compilations for the time being. This allows library authors
    eager to make their code future compatible to adapt to new features before
    they even generate warnings.

    This currently enables :ghc-flag:`-Wmissing-monadfail-instance`,
    :ghc-flag:`-Wsemigroup`, and :ghc-flag:`-Wnoncanonical-monoid-instances`.

.. ghc-flag:: -Wno-compat

    Disables all warnings enabled by :ghc-flag:`-Wcompat`.

.. ghc-flag:: -w

    Turns off all warnings, including the standard ones and those that
    :ghc-flag:`-Wall` doesn't enable.

.. ghc-flag:: -Werror

    Makes any warning into a fatal error. Useful so that you don't miss
    warnings when doing batch compilation.

.. ghc-flag:: -Wwarn

    Warnings are treated only as warnings, not as errors. This is the
    default, but can be useful to negate a :ghc-flag:`-Werror` flag.

The full set of warning options is described below. To turn off any
warning, simply give the corresponding ``-Wno-...`` option on the
command line. For backwards compatibility with GHC versions prior to 8.0,
all these warnings can still be controlled with ``-f(no-)warn-*`` instead
of ``-W(no-)*``.

.. ghc-flag:: -Wtyped-holes

    Determines whether the compiler reports typed holes warnings. Has no
    effect unless typed holes errors are deferred until runtime. See
    :ref:`typed-holes` and :ref:`defer-type-errors`

    This warning is on by default.

.. ghc-flag:: -Wtype-errors

    Causes a warning to be reported when a type error is deferred until
    runtime. See :ref:`defer-type-errors`

    This warning is on by default.

.. ghc-flag:: -fdefer-type-errors

    :implies: :ghc-flag:`-fdefer-typed-holes`

    Defer as many type errors as possible until runtime. At compile time
    you get a warning (instead of an error). At runtime, if you use a
    value that depends on a type error, you get a runtime error; but you
    can run any type-correct parts of your code just fine. See
    :ref:`defer-type-errors`

.. ghc-flag:: -fdefer-typed-holes

    Defer typed holes errors until runtime. This will turn the errors
    produced by :ref:`typed holes <typed-holes>` into warnings. Using a value
    that depends on a typed hole produces a runtime error, the same as
    :ghc-flag:`-fdefer-type-errors` (which implies this option). See :ref:`typed-holes`
    and :ref:`defer-type-errors`.

    Implied by :ghc-flag:`-fdefer-type-errors`. See also :ghc-flag:`-Wtyped-holes`.

.. ghc-flag:: -Wpartial-type-signatures

    Determines whether the compiler reports holes in partial type
    signatures as warnings. Has no effect unless
    :ghc-flag:`-XPartialTypeSignatures` is enabled, which controls whether
    errors should be generated for holes in types or not. See
    :ref:`partial-type-signatures`.

    This warning is on by default.

.. ghc-flag:: -fhelpful-errors

    When a name or package is not found in scope, make suggestions for
    the name or package you might have meant instead.

    This option is on by default.

.. ghc-flag:: -Wunrecognised-pragmas

    Causes a warning to be emitted when a pragma that GHC doesn't
    recognise is used. As well as pragmas that GHC itself uses, GHC also
    recognises pragmas known to be used by other tools, e.g.
    ``OPTIONS_HUGS`` and ``DERIVE``.

    This option is on by default.

.. ghc-flag:: -Wmissed-specialisations
              -Wall-missed-specialisations

    Emits a warning if GHC cannot specialise an overloaded function, usually
    because the function needs an ``INLINEABLE`` pragma. The "all" form reports
    all such situations whereas the "non-all" form only reports when the
    situation arises during specialisation of an imported function.

    The "non-all" form is intended to catch cases where an imported function
    that is marked as ``INLINEABLE`` (presumably to enable specialisation) cannot
    be specialised as it calls other functions that are themselves not specialised.

    These options are both off by default.

.. ghc-flag:: -Wwarnings-deprecations

    .. index::
       pair: deprecations; warnings

    Causes a warning to be emitted when a module, function or type with
    a ``WARNING`` or ``DEPRECATED pragma`` is used. See
    :ref:`warning-deprecated-pragma` for more details on the pragmas.

    This option is on by default.

.. ghc-flag:: -Wamp

    .. index::
       single: AMP
       single: Applicative-Monad Proposal

    This option is deprecated.

    Caused a warning to be emitted when a definition was in conflict with
    the AMP (Applicative-Monad proosal).

.. ghc-flag:: -Wnoncanonical-monad-instances

    Warn if noncanonical ``Applicative`` or ``Monad`` instances
    declarations are detected.

    When this warning is enabled, the following conditions are verified:

    In ``Monad`` instances declarations warn if any of the following
    conditions does not hold:

     * If ``return`` is defined it must be canonical (i.e. ``return = pure``).
     * If ``(>>)`` is defined it must be canonical (i.e. ``(>>) = (*>)``).

    Moreover, in 'Applicative' instance declarations:

     * Warn if ``pure`` is defined backwards (i.e. ``pure = return``).
     * Warn if ``(*>)`` is defined backwards (i.e. ``(*>) = (>>)``).

    This option is off by default.

.. ghc-flag:: -Wnoncanonical-monoid-instances

    Warn if noncanonical ``Semigroup`` or ``Monoid`` instances
    declarations are detected.

    When this warning is enabled, the following conditions are verified:

    In ``Monoid`` instances declarations warn if any of the following
    conditions does not hold:

     * If ``mappend`` is defined it must be canonical
       (i.e. ``mappend = (Data.Semigroup.<>)``).

    Moreover, in 'Semigroup' instance declarations:

     * Warn if ``(<>)`` is defined backwards (i.e. ``(<>) = mappend``).

    This warning is off by default. However, it is part of the
    :ghc-flag:`-Wcompat` option group.

.. ghc-flag:: -Wmissing-monadfail-instance

    .. index::
       single: MFP
       single: MonadFail Proposal

    Warn when a failable pattern is used in a do-block that does not have a
    ``MonadFail`` instance.

    Being part of the :ghc-flag:`-Wcompat` option group, this warning is off by
    default, but will be switched on in a future GHC release, as part of
    the `MonadFail Proposal (MFP)
    <https://prime.haskell.org/wiki/Libraries/Proposals/MonadFail>`__.

.. ghc-flag:: -Wsemigroup

    .. index::
       single: semigroup; warning

    Warn when definitions are in conflict with the future inclusion of
    ``Semigroup`` into the standard typeclasses.

     1. Instances of ``Monoid`` should also be instances of ``Semigroup``
     2. The ``Semigroup`` operator ``(<>)`` will be in ``Prelude``, which
        clashes with custom local definitions of such an operator

    Being part of the :ghc-flag:`-Wcompat` option group, this warning is off by
    default, but will be switched on in a future GHC release.

.. ghc-flag:: -Wdeprecated-flags

    .. index::
       single: deprecated flags

    Causes a warning to be emitted when a deprecated command-line flag
    is used.

    This option is on by default.

.. ghc-flag:: -Wunsupported-calling-conventions

    Causes a warning to be emitted for foreign declarations that use
    unsupported calling conventions. In particular, if the ``stdcall``
    calling convention is used on an architecture other than i386 then
    it will be treated as ``ccall``.

.. ghc-flag:: -Wdodgy-foreign-imports

    Causes a warning to be emitted for foreign imports of the following
    form: ::

        foreign import "f" f :: FunPtr t

    on the grounds that it probably should be ::

        foreign import "&f" f :: FunPtr t

    The first form declares that \`f\` is a (pure) C function that takes
    no arguments and returns a pointer to a C function with type \`t\`,
    whereas the second form declares that \`f\` itself is a C function
    with type \`t\`. The first declaration is usually a mistake, and one
    that is hard to debug because it results in a crash, hence this
    warning.

.. ghc-flag:: -Wdodgy-exports

    Causes a warning to be emitted when a datatype ``T`` is exported
    with all constructors, i.e. ``T(..)``, but is it just a type
    synonym.

    Also causes a warning to be emitted when a module is re-exported,
    but that module exports nothing.

.. ghc-flag:: -Wdodgy-imports

    Causes a warning to be emitted in the following cases:

    -  When a datatype ``T`` is imported with all constructors, i.e.
       ``T(..)``, but has been exported abstractly, i.e. ``T``.

    -  When an ``import`` statement hides an entity that is not
       exported.

.. ghc-flag:: -Woverflowed-literals

    Causes a warning to be emitted if a literal will overflow, e.g.
    ``300 :: Word8``.

.. ghc-flag:: -Wempty-enumerations

    Causes a warning to be emitted if an enumeration is empty, e.g.
    ``[5 .. 3]``.

.. ghc-flag:: -Wlazy-unlifted-bindings

    This flag is a no-op, and will be removed in GHC 7.10.

.. ghc-flag:: -Wduplicate-constraints

    .. index::
       single: duplicate constraints, warning

    Have the compiler warn about duplicate constraints in a type
    signature. For example ::

        f :: (Eq a, Show a, Eq a) => a -> a

    The warning will indicate the duplicated ``Eq a`` constraint.

    This option is now deprecated in favour of
    :ghc-flag:`-Wredundant-constraints`.

.. ghc-flag:: -Wredundant-constraints

    .. index::
       single: redundant constraints, warning

    Have the compiler warn about redundant constraints in a type
    signature. In particular:

    -  A redundant constraint within the type signature itself: ::

            f :: (Eq a, Ord a) => a -> a

       The warning will indicate the redundant ``Eq a`` constraint: it
       is subsumed by the ``Ord a`` constraint.

    -  A constraint in the type signature is not used in the code it
       covers: ::

            f :: Eq a => a -> a -> Bool
            f x y = True

       The warning will indicate the redundant ``Eq a`` constraint: : it
       is not used by the definition of ``f``.)

    Similar warnings are given for a redundant constraint in an instance
    declaration.

    This option is on by default. As usual you can suppress it on a
    per-module basis with :ghc-flag:`-Wno-redundant-constraints`.
    Occasionally you may specifically want a function to have a more
    constrained signature than necessary, perhaps to leave yourself
    wiggle-room for changing the implementation without changing the
    API. In that case, you can suppress the warning on a per-function
    basis, using a call in a dead binding. For example: ::

        f :: Eq a => a -> a -> Bool
        f x y = True
        where
            _ = x == x  -- Suppress the redundant-constraint warning for (Eq a)

    Here the call to ``(==)`` makes GHC think that the ``(Eq a)``
    constraint is needed, so no warning is issued.

.. ghc-flag:: -Wduplicate-exports

    .. index::
       single: duplicate exports, warning
       single: export lists, duplicates

    Have the compiler warn about duplicate entries in export lists. This
    is useful information if you maintain large export lists, and want
    to avoid the continued export of a definition after you've deleted
    (one) mention of it in the export list.

    This option is on by default.

.. ghc-flag:: -Whi-shadowing

    .. index::
       single: shadowing; interface files

    Causes the compiler to emit a warning when a module or interface
    file in the current directory is shadowing one with the same module
    name in a library or other directory.

.. ghc-flag:: -Widentities

    Causes the compiler to emit a warning when a Prelude numeric
    conversion converts a type ``T`` to the same type ``T``; such calls are
    probably no-ops and can be omitted. The functions checked for are:
    ``toInteger``, ``toRational``, ``fromIntegral``, and ``realToFrac``.

.. ghc-flag:: -Wimplicit-prelude

    .. index::
       single: implicit prelude, warning

    Have the compiler warn if the Prelude is implicitly imported. This
    happens unless either the Prelude module is explicitly imported with
    an ``import ... Prelude ...`` line, or this implicit import is
    disabled (either by :ghc-flag:`-XNoImplicitPrelude` or a
    ``LANGUAGE NoImplicitPrelude`` pragma).

    Note that no warning is given for syntax that implicitly refers to
    the Prelude, even if :ghc-flag:`-XNoImplicitPrelude` would change whether it
    refers to the Prelude. For example, no warning is given when ``368``
    means ``Prelude.fromInteger (368::Prelude.Integer)`` (where
    ``Prelude`` refers to the actual Prelude module, regardless of the
    imports of the module being compiled).

    This warning is off by default.

.. ghc-flag:: -Wincomplete-patterns
              -Wincomplete-uni-patterns

    .. index::
       single: incomplete patterns, warning
       single: patterns, incomplete

    The option :ghc-flag:`-Wincomplete-patterns` warns about places where a
    pattern-match might fail at runtime. The function ``g`` below will
    fail when applied to non-empty lists, so the compiler will emit a
    warning about this when :ghc-flag:`-Wincomplete-patterns` is enabled. ::

        g [] = 2

    This option isn't enabled by default because it can be a bit noisy,
    and it doesn't always indicate a bug in the program. However, it's
    generally considered good practice to cover all the cases in your
    functions, and it is switched on by :ghc-flag:`-W`.

    The flag :ghc-flag:`-Wincomplete-uni-patterns` is similar, except that
    it applies only to lambda-expressions and pattern bindings,
    constructs that only allow a single pattern: ::

        h = \[] -> 2
        Just k = f y

.. ghc-flag:: -Wincomplete-record-updates

    .. index::
       single: incomplete record updates, warning
       single: record updates, incomplete

    The function ``f`` below will fail when applied to ``Bar``, so the
    compiler will emit a warning about this when
    :ghc-flag:`-Wincomplete-record-updates` is enabled. ::

        data Foo = Foo { x :: Int }
                 | Bar

        f :: Foo -> Foo
        f foo = foo { x = 6 }

    This option isn't enabled by default because it can be very noisy,
    and it often doesn't indicate a bug in the program.

.. ghc-flag:: -Wtoo-many-guards
              -Wno-too-many-guards

    .. index::
       single: too many guards, warning

    The option :ghc-flag:`-Wtoo-many-guards` warns about places where a
    pattern match contains too many guards (over 20 at the moment).
    It has an effect only if any form of exhaustivness/overlapping
    checking is enabled (one of
    :ghc-flag:`-Wincomplete-patterns`,
    :ghc-flag:`-Wincomplete-uni-patterns`,
    :ghc-flag:`-Wincomplete-record-updates`,
    :ghc-flag:`-Woverlapping-patterns`). When enabled, the warning can be
    suppressed by enabling either :ghc-flag:`-Wno-too-many-guards`, which just
    hides the warning, or :ghc-flag:`-ffull-guard-reasoning` which runs the
    full check, independently of the number of guards.

.. ghc-flag:: -ffull-guard-reasoning

    :implies: :ghc-flag:`-Wno-too-many-guards`

    .. index::
       single: guard reasoning, warning

    The option :ghc-flag:`-ffull-guard-reasoning` forces pattern match checking
    to run in full. This gives more precise warnings concerning pattern
    guards but in most cases increases memory consumption and
    compilation time. Hence, it is off by default. Enabling
    :ghc-flag:`-ffull-guard-reasoning` also implies :ghc-flag:`-Wno-too-many-guards`.
    Note that (like :ghc-flag:`-Wtoo-many-guards`) :ghc-flag:`-ffull-guard-reasoning`
    makes a difference only if pattern match checking is already
    enabled.

.. ghc-flag:: -Wmissing-fields

    .. index::
       single: missing fields, warning
       single: fields, missing

    This option is on by default, and warns you whenever the
    construction of a labelled field constructor isn't complete, missing
    initialisers for one or more fields. While not an error (the missing
    fields are initialised with bottoms), it is often an indication of a
    programmer error.

.. ghc-flag:: -Wmissing-import-lists

    .. index::
       single: missing import lists, warning
       single: import lists, missing

    This flag warns if you use an unqualified ``import`` declaration
    that does not explicitly list the entities brought into scope. For
    example ::

        module M where
          import X( f )
          import Y
          import qualified Z
          p x = f x x

    The :ghc-flag:`-Wmissing-import-lists` flag will warn about the import of
    ``Y`` but not ``X`` If module ``Y`` is later changed to export (say) ``f``,
    then the reference to ``f`` in ``M`` will become ambiguous. No warning is
    produced for the import of ``Z`` because extending ``Z``\'s exports would be
    unlikely to produce ambiguity in ``M``.

.. ghc-flag:: -Wmissing-methods

    .. index::
       single: missing methods, warning
       single: methods, missing

    This option is on by default, and warns you whenever an instance
    declaration is missing one or more methods, and the corresponding
    class declaration has no default declaration for them.

    The warning is suppressed if the method name begins with an
    underscore. Here's an example where this is useful: ::

        class C a where
            _simpleFn :: a -> String
            complexFn :: a -> a -> String
            complexFn x y = ... _simpleFn ...

    The idea is that: (a) users of the class will only call
    ``complexFn``; never ``_simpleFn``; and (b) instance declarations
    can define either ``complexFn`` or ``_simpleFn``.

    The ``MINIMAL`` pragma can be used to change which combination of
    methods will be required for instances of a particular class. See
    :ref:`minimal-pragma`.

.. ghc-flag:: -Wmissing-signatures

    .. index::
       single: type signatures, missing

    If you would like GHC to check that every top-level function/value
    has a type signature, use the :ghc-flag:`-Wmissing-signatures` option.
    As part of the warning GHC also reports the inferred type. The
    option is off by default.

.. ghc-flag:: -Wmissing-exported-sigs

    .. index::
       single: type signatures, missing

    If you would like GHC to check that every exported top-level
    function/value has a type signature, but not check unexported
    values, use the :ghc-flag:`-Wmissing-exported-sigs` option. This option
    takes precedence over :ghc-flag:`-Wmissing-signatures`. As part of the
    warning GHC also reports the inferred type. The option is off by
    default.

.. ghc-flag:: -Wmissing-local-sigs

    .. index::
       single: type signatures, missing

    If you use the :ghc-flag:`-Wmissing-local-sigs` flag GHC will warn you
    about any polymorphic local bindings. As part of the warning GHC
    also reports the inferred type. The option is off by default.

.. ghc-flag:: -Wmissing-pat-syn-sigs

    .. index::
         single: type signatures, missing, pattern synonyms

    If you would like GHC to check that every pattern synonym has a type
    signature, use the :ghc-flag:`-Wmissing-pat-syn-sigs` option. If this option is
    used in conjunction with :ghc-flag:`-Wmissing-exported-sigs` then only
    exported pattern synonyms must have a type signature. GHC also reports the
    inferred type. This option is off by default.

.. ghc-flag:: -Wname-shadowing

    .. index::
       single: shadowing, warning

    This option causes a warning to be emitted whenever an inner-scope
    value has the same name as an outer-scope value, i.e. the inner
    value shadows the outer one. This can catch typographical errors
    that turn into hard-to-find bugs, e.g., in the inadvertent capture
    of what would be a recursive call in
    ``f = ... let f = id in ... f ...``.

    The warning is suppressed for names beginning with an underscore.
    For example ::

        f x = do { _ignore <- this; _ignore <- that; return (the other) }

.. ghc-flag:: -Worphans

    .. index::
       single: orphan instances, warning
       single: orphan rules, warning

    These flags cause a warning to be emitted whenever the module
    contains an "orphan" instance declaration or rewrite rule. An
    instance declaration is an orphan if it appears in a module in which
    neither the class nor the type being instanced are declared in the
    same module. A rule is an orphan if it is a rule for a function
    declared in another module. A module containing any orphans is
    called an orphan module.

    The trouble with orphans is that GHC must pro-actively read the
    interface files for all orphan modules, just in case their instances
    or rules play a role, whether or not the module's interface would
    otherwise be of any use. See :ref:`orphan-modules` for details.

    The flag :ghc-flag:`-Worphans` warns about user-written orphan rules or
    instances.

.. ghc-flag:: -Woverlapping-patterns

    .. index::
       single: overlapping patterns, warning
       single: patterns, overlapping

    By default, the compiler will warn you if a set of patterns are
    overlapping, e.g., ::

        f :: String -> Int
        f []     = 0
        f (_:xs) = 1
        f "2"    = 2

    where the last pattern match in ``f`` won't ever be reached, as the
    second pattern overlaps it. More often than not, redundant patterns
    is a programmer mistake/error, so this option is enabled by default.

.. ghc-flag:: -Wtabs

    .. index::
       single: tabs, warning

    Have the compiler warn if there are tabs in your source file.

.. ghc-flag:: -Wtype-defaults

    .. index::
       single: defaulting mechanism, warning

    Have the compiler warn/inform you where in your source the Haskell
    defaulting mechanism for numeric types kicks in. This is useful
    information when converting code from a context that assumed one
    default into one with another, e.g., the ‘default default’ for
    Haskell 1.4 caused the otherwise unconstrained value ``1`` to be
    given the type ``Int``, whereas Haskell 98 and later defaults it to
    ``Integer``. This may lead to differences in performance and
    behaviour, hence the usefulness of being non-silent about this.

    This warning is off by default.

.. ghc-flag:: -Wmonomorphism-restriction

    .. index::
       single: monomorphism restriction, warning

    Have the compiler warn/inform you where in your source the Haskell
    Monomorphism Restriction is applied. If applied silently the MR can
    give rise to unexpected behaviour, so it can be helpful to have an
    explicit warning that it is being applied.

    This warning is off by default.

.. ghc-flag:: -Wunsupported-llvm-version

    Warn when using :ghc-flag:`-fllvm` with an unsupported version of LLVM.

.. ghc-flag:: -Wunticked-promoted-constructors

    .. index::
       single: promoted constructor, warning

    Warn if a promoted data constructor is used without a tick preceding
    its name.

    For example: ::

        data Nat = Succ Nat | Zero

        data Vec n s where
          Nil  :: Vec Zero a
          Cons :: a -> Vec n a -> Vec (Succ n) a

    Will raise two warnings because ``Zero`` and ``Succ`` are not
    written as ``'Zero`` and ``'Succ``.

    This warning is is enabled by default in :ghc-flag:`-Wall` mode.

.. ghc-flag:: -Wunused-binds

    .. index::
       single: unused binds, warning
       single: binds, unused

    Report any function definitions (and local bindings) which are
    unused. An alias for

    -  :ghc-flag:`-Wunused-top-binds`
    -  :ghc-flag:`-Wunused-local-binds`
    -  :ghc-flag:`-Wunused-pattern-binds`

.. ghc-flag:: -Wunused-top-binds

    .. index::
       single: unused binds, warning
       single: binds, unused

    Report any function definitions which are unused.

    More precisely, warn if a binding brings into scope a variable that
    is not used, except if the variable's name starts with an
    underscore. The "starts-with-underscore" condition provides a way to
    selectively disable the warning.

    A variable is regarded as "used" if

    -  It is exported, or

    -  It appears in the right hand side of a binding that binds at
       least one used variable that is used

    For example: ::

        module A (f) where
        f = let (p,q) = rhs1 in t p  -- No warning: q is unused, but is locally bound
        t = rhs3                     -- No warning: f is used, and hence so is t
        g = h x                      -- Warning: g unused
        h = rhs2                     -- Warning: h is only used in the
                                     -- right-hand side of another unused binding
        _w = True                    -- No warning: _w starts with an underscore

.. ghc-flag:: -Wunused-local-binds

    .. index::
       single: unused binds, warning
       single: binds, unused

    Report any local definitions which are unused. For example: ::

        module A (f) where
        f = let (p,q) = rhs1 in t p  -- Warning: q is unused
        g = h x                      -- No warning: g is unused, but is a top-level binding

.. ghc-flag:: -Wunused-pattern-binds

    .. index::
       single: unused binds, warning
       single: binds, unused

    Warn if a pattern binding binds no variables at all, unless it is a
    lone, possibly-banged, wild-card pattern. For example: ::

        Just _ = rhs3    -- Warning: unused pattern binding
        (_, _) = rhs4    -- Warning: unused pattern binding
        _  = rhs3        -- No warning: lone wild-card pattern
        !_ = rhs4        -- No warning: banged wild-card pattern; behaves like seq

    The motivation for allowing lone wild-card patterns is they are not
    very different from ``_v = rhs3``, which elicits no warning; and
    they can be useful to add a type constraint, e.g. ``_ = x::Int``. A
    lone banged wild-card pattern is useful as an alternative (to
    ``seq``) way to force evaluation.

.. ghc-flag:: -Wunused-imports

    .. index::
       single: unused imports, warning
       single: imports, unused

    Report any modules that are explicitly imported but never used.
    However, the form ``import M()`` is never reported as an unused
    import, because it is a useful idiom for importing instance
    declarations, which are anonymous in Haskell.

.. ghc-flag:: -Wunused-matches

    .. index::
       single: unused matches, warning
       single: matches, unused

    Report all unused variables which arise from pattern matches,
    including patterns consisting of a single variable. This includes
    unused type variables in type family instances. For instance
    ``f x y = []`` would report ``x`` and ``y`` as unused. The warning
    is suppressed if the variable name begins with an underscore, thus: ::

        f _x = True

.. ghc-flag:: -Wunused-do-bind

    .. index::
       single: unused do binding, warning
       single: do binding, unused

    Report expressions occurring in ``do`` and ``mdo`` blocks that
    appear to silently throw information away. For instance
    ``do { mapM popInt xs ; return 10 }`` would report the first
    statement in the ``do`` block as suspicious, as it has the type
    ``StackM [Int]`` and not ``StackM ()``, but that ``[Int]`` value is
    not bound to anything. The warning is suppressed by explicitly
    mentioning in the source code that your program is throwing
    something away: ::

        do { _ <- mapM popInt xs ; return 10 }

    Of course, in this particular situation you can do even better: ::

        do { mapM_ popInt xs ; return 10 }

.. ghc-flag:: -Wwrong-do-bind

    .. index::
       single: apparently erroneous do binding, warning
       single: do binding, apparently erroneous

    Report expressions occurring in ``do`` and ``mdo`` blocks that
    appear to lack a binding. For instance
    ``do { return (popInt 10) ; return 10 }`` would report the first
    statement in the ``do`` block as suspicious, as it has the type
    ``StackM (StackM Int)`` (which consists of two nested applications
    of the same monad constructor), but which is not then "unpacked" by
    binding the result. The warning is suppressed by explicitly
    mentioning in the source code that your program is throwing
    something away: ::

        do { _ <- return (popInt 10) ; return 10 }

    For almost all sensible programs this will indicate a bug, and you
    probably intended to write: ::

        do { popInt 10 ; return 10 }

.. ghc-flag:: -Winline-rule-shadowing

    Warn if a rewrite RULE might fail to fire because the function might
    be inlined before the rule has a chance to fire. See
    :ref:`rules-inline`.

If you're feeling really paranoid, the :ghc-flag:`-dcore-lint` option is a good choice.
It turns on heavyweight intra-pass sanity-checking within GHC. (It checks GHC's
sanity, not yours.)

