%
% (c) The AQUA Project, Glasgow University, 1996-1998
%
\section[RnHsSyn]{Specialisations of the @HsSyn@ syntax for the renamer}

\begin{code}
module RnHsSyn where

#include "HsVersions.h"

import HsSyn
import HsCore
import Class		( FunDep )
import TysWiredIn	( tupleTyCon, listTyCon, charTyCon )
import Name		( Name, getName, isTyVarName )
import NameSet
import BasicTypes	( Boxity )
import Maybes		( orElse )
import Outputable
\end{code}


\begin{code}
type RenamedArithSeqInfo	= ArithSeqInfo		Name RenamedPat
type RenamedClassOpSig		= Sig			Name
type RenamedConDecl		= ConDecl		Name
type RenamedContext		= HsContext 		Name
type RenamedHsDecl		= HsDecl		Name RenamedPat
type RenamedRuleDecl		= RuleDecl		Name RenamedPat
type RenamedTyClDecl		= TyClDecl		Name RenamedPat
type RenamedDefaultDecl		= DefaultDecl		Name
type RenamedForeignDecl		= ForeignDecl		Name
type RenamedGRHS		= GRHS			Name RenamedPat
type RenamedGRHSs		= GRHSs			Name RenamedPat
type RenamedHsBinds		= HsBinds		Name RenamedPat
type RenamedHsExpr		= HsExpr		Name RenamedPat
type RenamedHsModule		= HsModule		Name RenamedPat
type RenamedInstDecl		= InstDecl		Name RenamedPat
type RenamedMatch		= Match			Name RenamedPat
type RenamedMonoBinds		= MonoBinds		Name RenamedPat
type RenamedPat			= InPat			Name
type RenamedHsType		= HsType		Name
type RenamedHsPred		= HsPred		Name
type RenamedRecordBinds		= HsRecordBinds		Name RenamedPat
type RenamedSig			= Sig			Name
type RenamedStmt		= Stmt			Name RenamedPat
type RenamedFixitySig		= FixitySig		Name
type RenamedDeprecation		= DeprecDecl		Name
type RenamedHsOverLit		= HsOverLit		Name
\end{code}

%************************************************************************
%*									*
\subsection{Free variables}
%*									*
%************************************************************************

These free-variable finders returns tycons and classes too.

\begin{code}
charTyCon_name, listTyCon_name :: Name
charTyCon_name    = getName charTyCon
listTyCon_name    = getName listTyCon

tupleTyCon_name :: Boxity -> Int -> Name
tupleTyCon_name boxity n = getName (tupleTyCon boxity n)

extractHsTyVars :: RenamedHsType -> NameSet
extractHsTyVars x = filterNameSet isTyVarName (extractHsTyNames x)

extractFunDepNames :: FunDep Name -> NameSet
extractFunDepNames (ns1, ns2) = mkNameSet ns1 `unionNameSets` mkNameSet ns2

extractHsTyNames   :: RenamedHsType -> NameSet
extractHsTyNames ty
  = get ty
  where
    get (HsAppTy ty1 ty2)      = get ty1 `unionNameSets` get ty2
    get (HsListTy ty)          = unitNameSet listTyCon_name `unionNameSets` get ty
    get (HsTupleTy (HsTupCon n _) tys) = unitNameSet n
				   	 `unionNameSets` extractHsTyNames_s tys
    get (HsFunTy ty1 ty2)      = get ty1 `unionNameSets` get ty2
    get (HsPredTy p)	       = extractHsPredTyNames p
    get (HsOpTy ty1 tycon ty2) = get ty1 `unionNameSets` get ty2 `unionNameSets`
				 unitNameSet tycon
    get (HsNumTy n)            = emptyNameSet
    get (HsTyVar tv)	       = unitNameSet tv
    get (HsForAllTy (Just tvs) 
		    ctxt ty)   = (extractHsCtxtTyNames ctxt `unionNameSets` get ty)
					    `minusNameSet`
				  mkNameSet (hsTyVarNames tvs)
    get ty@(HsForAllTy Nothing _ _) = pprPanic "extractHsTyNames" (ppr ty)

extractHsTyNames_s  :: [RenamedHsType] -> NameSet
extractHsTyNames_s tys = foldr (unionNameSets . extractHsTyNames) emptyNameSet tys

extractHsCtxtTyNames :: RenamedContext -> NameSet
extractHsCtxtTyNames ctxt = foldr (unionNameSets . extractHsPredTyNames) emptyNameSet ctxt

-- You don't import or export implicit parameters,
-- so don't mention the IP names
extractHsPredTyNames (HsPClass cls tys)
  = unitNameSet cls `unionNameSets` extractHsTyNames_s tys
extractHsPredTyNames (HsPIParam n ty)
  = extractHsTyNames ty
\end{code}


%************************************************************************
%*									*
\subsection{Free variables of declarations}
%*									*
%************************************************************************

Return the Names that must be in scope if we are to use this declaration.
In all cases this is set up for interface-file declarations:
	- for class decls we ignroe the bindings
	- for instance decls likewise, plus the pragmas
	- for rule decls, we ignore HsRules

\begin{code}
tyClDeclFVs :: RenamedTyClDecl -> NameSet
tyClDeclFVs (IfaceSig {tcdType = ty, tcdIdInfo = id_infos})
  = extractHsTyNames ty			`plusFV` 
    plusFVs (map hsIdInfoFVs id_infos)

tyClDeclFVs (TyData {tcdCtxt = context, tcdTyVars = tyvars, tcdCons = condecls, tcdDerivs = derivings})
  = delFVs (map hsTyVarName tyvars) $
    extractHsCtxtTyNames context	`plusFV`
    plusFVs (map conDeclFVs condecls)	`plusFV`
    mkNameSet (derivings `orElse` [])

tyClDeclFVs (TySynonym {tcdTyVars = tyvars, tcdSynRhs = ty})
  = delFVs (map hsTyVarName tyvars) (extractHsTyNames ty)

tyClDeclFVs (ClassDecl {tcdCtxt = context, tcdTyVars = tyvars, tcdFDs = fds, tcdSigs = sigs})
  = delFVs (map hsTyVarName tyvars) $
    extractHsCtxtTyNames context	  `plusFV`
    plusFVs (map extractFunDepNames fds)  `plusFV`
    hsSigsFVs sigs

----------------
hsSigsFVs sigs = plusFVs (map hsSigFVs sigs)

hsSigFVs (Sig v ty _) 	    = extractHsTyNames ty
hsSigFVs (SpecInstSig ty _) = extractHsTyNames ty
hsSigFVs (SpecSig v ty _)   = extractHsTyNames ty
hsSigFVs (ClassOpSig _ _ ty _) = extractHsTyNames ty
hsSigFVs other		    = emptyFVs

----------------
instDeclFVs (InstDecl inst_ty _ _ maybe_dfun _)
  = extractHsTyNames inst_ty	`plusFV` 
    (case maybe_dfun of { Just n -> unitFV n; Nothing -> emptyFVs })

----------------
ruleDeclFVs (HsRule _ _ _ _ _ _) = emptyFVs
ruleDeclFVs (IfaceRule _ vars _ args rhs _)
  = delFVs (map ufBinderName vars) $
    ufExprFVs rhs `plusFV` plusFVs (map ufExprFVs args)

----------------
conDeclFVs (ConDecl _ _ tyvars context details _)
  = delFVs (map hsTyVarName tyvars) $
    extractHsCtxtTyNames context	  `plusFV`
    conDetailsFVs details

conDetailsFVs (VanillaCon btys)    = plusFVs (map bangTyFVs btys)
conDetailsFVs (InfixCon bty1 bty2) = bangTyFVs bty1 `plusFV` bangTyFVs bty2
conDetailsFVs (RecCon flds)	   = plusFVs [bangTyFVs bty | (_, bty) <- flds]

bangTyFVs bty = extractHsTyNames (getBangType bty)

----------------
hsIdInfoFVs (HsUnfold _ unf) = ufExprFVs unf
hsIdInfoFVs (HsWorker n)     = unitFV n
hsIdInfoFVs other	     = emptyFVs

----------------
ufExprFVs (UfVar n) 	  = unitFV n
ufExprFVs (UfLit l) 	  = emptyFVs
ufExprFVs (UfLitLit l ty) = extractHsTyNames ty
ufExprFVs (UfCCall cc ty) = extractHsTyNames ty
ufExprFVs (UfType ty)     = extractHsTyNames ty
ufExprFVs (UfTuple tc es) = hsTupConFVs tc `plusFV` plusFVs (map ufExprFVs es)
ufExprFVs (UfLam v e)     = ufBndrFVs v (ufExprFVs e)
ufExprFVs (UfApp e1 e2)   = ufExprFVs e1 `plusFV` ufExprFVs e2
ufExprFVs (UfCase e n as) = ufExprFVs e `plusFV` delFV n (plusFVs (map ufAltFVs as))
ufExprFVs (UfNote n e)	  = ufNoteFVs n `plusFV` ufExprFVs e
ufExprFVs (UfLet (UfNonRec b r) e) = ufExprFVs r `plusFV` ufBndrFVs b (ufExprFVs e)
ufExprFVs (UfLet (UfRec prs)    e) = foldr ufBndrFVs 
					   (foldr (plusFV . ufExprFVs . snd) (ufExprFVs e) prs)
					   (map fst prs) 

ufBndrFVs (UfValBinder n ty) fvs = extractHsTyNames ty `plusFV` delFV n fvs
ufBndrFVs (UfTyBinder  n k)  fvs = delFV n fvs

ufAltFVs (con, vs, e) = ufConFVs con `plusFV` delFVs vs (ufExprFVs e)

ufConFVs (UfDataAlt n)      = unitFV n
ufConFVs (UfTupleAlt t)     = hsTupConFVs t
ufConFVs (UfLitLitAlt _ ty) = extractHsTyNames ty
ufConFVs other		    = emptyFVs

ufNoteFVs (UfCoerce ty) = extractHsTyNames ty
ufNoteFVs note		= emptyFVs

hsTupConFVs (HsTupCon n _) = unitFV n
\end{code}

%************************************************************************
%*									*
\subsection{A few functions on generic defintions
%*									*
%************************************************************************

These functions on generics are defined over RenamedMatches, which is
why they are here and not in HsMatches.

\begin{code}
maybeGenericMatch :: RenamedMatch -> Maybe (RenamedHsType, RenamedMatch)
  -- Tells whether a Match is for a generic definition
  -- and extract the type from a generic match and put it at the front

maybeGenericMatch (Match tvs (TypePatIn ty : pats) sig_ty grhss)
  = Just (ty, Match tvs pats sig_ty grhss)

maybeGenericMatch other_match = Nothing
\end{code}
