1c1
< //===- StmtOpenACC.h - Classes for OpenACC directives  ------------*- C++ -*-===//
---
> //===- StmtOpenMP.h - Classes for OpenMP directives  ------------*- C++ -*-===//
10c10
< /// \brief This file defines OpenACC AST classes for executable directives and
---
> /// \brief This file defines OpenMP AST classes for executable directives and
19c19
< #include "clang/AST/OpenACCClause.h"
---
> #include "clang/AST/OpenMPClause.h"
21c21
< #include "clang/Basic/OpenACCKinds.h"
---
> #include "clang/Basic/OpenMPKinds.h"
30c30
< /// \brief This is a basic class for representing single OpenACC executable
---
> /// \brief This is a basic class for representing single OpenMP executable
33c33
< class ACCExecutableDirective : public Stmt {
---
> class OMPExecutableDirective : public Stmt {
36c36
<   OpenACCDirectiveKind Kind;
---
>   OpenMPDirectiveKind Kind;
52,53c52,53
<   MutableArrayRef<ACCClause *> getClauses() {
<     ACCClause **ClauseStorage = reinterpret_cast<ACCClause **>(
---
>   MutableArrayRef<OMPClause *> getClauses() {
>     OMPClause **ClauseStorage = reinterpret_cast<OMPClause **>(
55c55
<     return MutableArrayRef<ACCClause *>(ClauseStorage, NumClauses);
---
>     return MutableArrayRef<OMPClause *>(ClauseStorage, NumClauses);
62c62
<   /// \param K Kind of OpenACC directive.
---
>   /// \param K Kind of OpenMP directive.
67c67
<   ACCExecutableDirective(const T *, StmtClass SC, OpenACCDirectiveKind K,
---
>   OMPExecutableDirective(const T *, StmtClass SC, OpenMPDirectiveKind K,
73c73
<         ClausesOffset(llvm::alignTo(sizeof(T), alignof(ACCClause *))) {}
---
>         ClausesOffset(llvm::alignTo(sizeof(T), alignof(OMPClause *))) {}
79c79
<   void setClauses(ArrayRef<ACCClause *> Clauses);
---
>   void setClauses(ArrayRef<OMPClause *> Clauses);
99c99
<             ArrayRef<ACCClause *>::const_iterator, std::forward_iterator_tag,
---
>             ArrayRef<OMPClause *>::const_iterator, std::forward_iterator_tag,
102c102
<     ArrayRef<ACCClause *>::const_iterator End;
---
>     ArrayRef<OMPClause *>::const_iterator End;
110c110
<     explicit specific_clause_iterator(ArrayRef<ACCClause *> Clauses)
---
>     explicit specific_clause_iterator(ArrayRef<OMPClause *> Clauses)
130c130
<   getClausesOfKind(ArrayRef<ACCClause *> Clauses) {
---
>   getClausesOfKind(ArrayRef<OMPClause *> Clauses) {
190c190
<   ACCClause *getClause(unsigned i) const { return clauses()[i]; }
---
>   OMPClause *getClause(unsigned i) const { return clauses()[i]; }
209,211c209,211
<   const CapturedStmt *getCapturedStmt(OpenACCDirectiveKind RegionKind) const {
<     SmallVector<OpenACCDirectiveKind, 4> CaptureRegions;
<     getOpenACCCaptureRegions(CaptureRegions, getDirectiveKind());
---
>   const CapturedStmt *getCapturedStmt(OpenMPDirectiveKind RegionKind) const {
>     SmallVector<OpenMPDirectiveKind, 4> CaptureRegions;
>     getOpenMPCaptureRegions(CaptureRegions, getDirectiveKind());
214,215c214,215
<                [=](const OpenACCDirectiveKind K) { return K == RegionKind; }) &&
<            "RegionKind not found in OpenACC CaptureRegions.");
---
>                [=](const OpenMPDirectiveKind K) { return K == RegionKind; }) &&
>            "RegionKind not found in OpenMP CaptureRegions.");
229,230c229,230
<     SmallVector<OpenACCDirectiveKind, 4> CaptureRegions;
<     getOpenACCCaptureRegions(CaptureRegions, getDirectiveKind());
---
>     SmallVector<OpenMPDirectiveKind, 4> CaptureRegions;
>     getOpenMPCaptureRegions(CaptureRegions, getDirectiveKind());
240c240
<     return const_cast<ACCExecutableDirective *>(this)
---
>     return const_cast<OMPExecutableDirective *>(this)
244c244
<   OpenACCDirectiveKind getDirectiveKind() const { return Kind; }
---
>   OpenMPDirectiveKind getDirectiveKind() const { return Kind; }
247,248c247,248
<      return S->getStmtClass() >= firstACCExecutableDirectiveConstant &&
<            S->getStmtClass() <= lastACCExecutableDirectiveConstant;
---
>     return S->getStmtClass() >= firstOMPExecutableDirectiveConstant &&
>            S->getStmtClass() <= lastOMPExecutableDirectiveConstant;
258c258
<   ArrayRef<ACCClause *> clauses() { return getClauses(); }
---
>   ArrayRef<OMPClause *> clauses() { return getClauses(); }
260,261c260,261
<   ArrayRef<ACCClause *> clauses() const {
<     return const_cast<ACCExecutableDirective *>(this)->getClauses();
---
>   ArrayRef<OMPClause *> clauses() const {
>     return const_cast<OMPExecutableDirective *>(this)->getClauses();
265c265
< /// \brief This represents '#pragma acc parallel' directive.
---
> /// \brief This represents '#pragma omp parallel' directive.
268c268
< /// #pragma acc parallel private(a,b) reduction(+: c,d)
---
> /// #pragma omp parallel private(a,b) reduction(+: c,d)
270c270
< /// In this example directive '#pragma acc parallel' has clauses 'private'
---
> /// In this example directive '#pragma omp parallel' has clauses 'private'
274c274
< class ACCParallelDirective : public ACCExecutableDirective {
---
> class OMPParallelDirective : public OMPExecutableDirective {
284c284
<   ACCParallelDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPParallelDirective(SourceLocation StartLoc, SourceLocation EndLoc,
286c286
<       : ACCExecutableDirective(this, ACCParallelDirectiveClass, ACCD_parallel,
---
>       : OMPExecutableDirective(this, OMPParallelDirectiveClass, OMPD_parallel,
294,295c294,295
<   explicit ACCParallelDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCParallelDirectiveClass, ACCD_parallel,
---
>   explicit OMPParallelDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPParallelDirectiveClass, OMPD_parallel,
313c313
<   static ACCParallelDirective *
---
>   static OMPParallelDirective *
315c315
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel);
322c322
<   static ACCParallelDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPParallelDirective *CreateEmpty(const ASTContext &C,
329c329
<     return T->getStmtClass() == ACCParallelDirectiveClass;
---
>     return T->getStmtClass() == OMPParallelDirectiveClass;
333,334c333,334
< /// \brief This is a common base class for loop directives ('acc simd', 'acc
< /// for', 'acc for simd' etc.). It is responsible for the loop code generation.
---
> /// \brief This is a common base class for loop directives ('omp simd', 'omp
> /// for', 'omp for simd' etc.). It is responsible for the loop code generation.
336c336
< class ACCLoopDirective : public ACCExecutableDirective {
---
> class OMPLoopDirective : public OMPExecutableDirective {
343c343
<   /// expressions stored in ACCLoopDirective.
---
>   /// expressions stored in OMPLoopDirective.
440c440
<   /// \param Kind Kind of OpenACC directive.
---
>   /// \param Kind Kind of OpenMP directive.
448c448
<   ACCLoopDirective(const T *That, StmtClass SC, OpenACCDirectiveKind Kind,
---
>   OMPLoopDirective(const T *That, StmtClass SC, OpenMPDirectiveKind Kind,
452c452
<       : ACCExecutableDirective(That, SC, Kind, StartLoc, EndLoc, NumClauses,
---
>       : OMPExecutableDirective(That, SC, Kind, StartLoc, EndLoc, NumClauses,
458,459c458,459
<   static unsigned getArraysOffset(OpenACCDirectiveKind Kind) {
<     if (isOpenACCLoopBoundSharingDirective(Kind))
---
>   static unsigned getArraysOffset(OpenMPDirectiveKind Kind) {
>     if (isOpenMPLoopBoundSharingDirective(Kind))
461,462c461,462
<     if (isOpenACCWorksharingDirective(Kind) || isOpenACCTaskLoopDirective(Kind) ||
<         isOpenACCDistributeDirective(Kind))
---
>     if (isOpenMPWorksharingDirective(Kind) || isOpenMPTaskLoopDirective(Kind) ||
>         isOpenMPDistributeDirective(Kind))
469c469
<                                   OpenACCDirectiveKind Kind) {
---
>                                   OpenMPDirectiveKind Kind) {
496,498c496,498
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
503,505c503,505
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
510,512c510,512
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
517,519c517,519
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
524,526c524,526
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
531,533c531,533
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
538,540c538,540
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
545,547c545,547
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
552c552
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
557c557
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
562c562
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
567c567
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
572c572
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
577c577
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
582c582
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
587c587
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
592c592
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
597c597
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
602c602
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
613,614c613,614
<   /// The expressions built to support OpenACC loops in combined/composite
<   /// pragmas (e.g. pragma acc distribute parallel for)
---
>   /// The expressions built to support OpenMP loops in combined/composite
>   /// pragmas (e.g. pragma omp distribute parallel for)
616,617c616,617
<     /// DistributeLowerBound - used when composing 'acc distribute' with
<     /// 'acc for' in a same construct.
---
>     /// DistributeLowerBound - used when composing 'omp distribute' with
>     /// 'omp for' in a same construct.
619,620c619,620
<     /// DistributeUpperBound - used when composing 'acc distribute' with
<     /// 'acc for' in a same construct.
---
>     /// DistributeUpperBound - used when composing 'omp distribute' with
>     /// 'omp for' in a same construct.
622,623c622,623
<     /// DistributeEnsureUpperBound - used when composing 'acc distribute'
<     ///  with 'acc for' in a same construct, EUB depends on DistUB
---
>     /// DistributeEnsureUpperBound - used when composing 'omp distribute'
>     ///  with 'omp for' in a same construct, EUB depends on DistUB
625c625
<     /// Distribute loop iteration variable init used when composing 'acc
---
>     /// Distribute loop iteration variable init used when composing 'omp
627c627
<     ///  with 'acc for' in a same construct
---
>     ///  with 'omp for' in a same construct
629,630c629,630
<     /// Distribute Loop condition used when composing 'acc distribute'
<     ///  with 'acc for' in a same construct
---
>     /// Distribute Loop condition used when composing 'omp distribute'
>     ///  with 'omp for' in a same construct
632c632
<     /// Update of LowerBound for statically sheduled acc loops for
---
>     /// Update of LowerBound for statically sheduled omp loops for
635c635
<     /// Update of UpperBound for statically sheduled acc loops for
---
>     /// Update of UpperBound for statically sheduled omp loops for
640c640
<   /// \brief The expressions built for the OpenACC loop CodeGen for the
---
>   /// \brief The expressions built for the OpenMP loop CodeGen for the
669c669
<     /// \brief Update of LowerBound for statically sheduled 'acc for' loops.
---
>     /// \brief Update of LowerBound for statically sheduled 'omp for' loops.
671c671
<     /// \brief Update of UpperBound for statically sheduled 'acc for' loops.
---
>     /// \brief Update of UpperBound for statically sheduled 'omp for' loops.
702c702
<     /// Expressions used when combining OpenACC loop pragmas
---
>     /// Expressions used when combining OpenMP loop pragmas
794,796c794,796
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
802,804c802,804
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
810,812c810,812
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
818,820c818,820
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
826,828c826,828
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
834,836c834,836
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
842,844c842,844
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
850,852c850,852
<     assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
<             isOpenACCTaskLoopDirective(getDirectiveKind()) ||
<             isOpenACCDistributeDirective(getDirectiveKind())) &&
---
>     assert((isOpenMPWorksharingDirective(getDirectiveKind()) ||
>             isOpenMPTaskLoopDirective(getDirectiveKind()) ||
>             isOpenMPDistributeDirective(getDirectiveKind())) &&
858c858
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
864c864
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
870c870
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
876c876
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
882c882
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
888c888
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
894c894
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
900c900
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
906c906
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
912c912
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
918c918
<     assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
---
>     assert(isOpenMPLoopBoundSharingDirective(getDirectiveKind()) &&
938c938
<     return const_cast<ACCLoopDirective *>(this)->getCounters();
---
>     return const_cast<OMPLoopDirective *>(this)->getCounters();
944c944
<     return const_cast<ACCLoopDirective *>(this)->getPrivateCounters();
---
>     return const_cast<OMPLoopDirective *>(this)->getPrivateCounters();
950c950
<     return const_cast<ACCLoopDirective *>(this)->getInits();
---
>     return const_cast<OMPLoopDirective *>(this)->getInits();
956c956
<     return const_cast<ACCLoopDirective *>(this)->getUpdates();
---
>     return const_cast<OMPLoopDirective *>(this)->getUpdates();
962c962
<     return const_cast<ACCLoopDirective *>(this)->getFinals();
---
>     return const_cast<OMPLoopDirective *>(this)->getFinals();
966,981c966,981
<     return T->getStmtClass() == ACCSimdDirectiveClass ||
<            T->getStmtClass() == ACCForDirectiveClass ||
<            T->getStmtClass() == ACCForSimdDirectiveClass ||
<            T->getStmtClass() == ACCParallelForDirectiveClass ||
<            T->getStmtClass() == ACCParallelForSimdDirectiveClass ||
<            T->getStmtClass() == ACCTaskLoopDirectiveClass ||
<            T->getStmtClass() == ACCTaskLoopSimdDirectiveClass ||
<            T->getStmtClass() == ACCDistributeDirectiveClass ||
<            T->getStmtClass() == ACCTargetParallelForDirectiveClass ||
<            T->getStmtClass() == ACCDistributeParallelForDirectiveClass ||
<            T->getStmtClass() == ACCDistributeParallelForSimdDirectiveClass ||
<            T->getStmtClass() == ACCDistributeSimdDirectiveClass ||
<            T->getStmtClass() == ACCTargetParallelForSimdDirectiveClass ||
<            T->getStmtClass() == ACCTargetSimdDirectiveClass ||
<            T->getStmtClass() == ACCTeamsDistributeDirectiveClass ||
<            T->getStmtClass() == ACCTeamsDistributeSimdDirectiveClass ||
---
>     return T->getStmtClass() == OMPSimdDirectiveClass ||
>            T->getStmtClass() == OMPForDirectiveClass ||
>            T->getStmtClass() == OMPForSimdDirectiveClass ||
>            T->getStmtClass() == OMPParallelForDirectiveClass ||
>            T->getStmtClass() == OMPParallelForSimdDirectiveClass ||
>            T->getStmtClass() == OMPTaskLoopDirectiveClass ||
>            T->getStmtClass() == OMPTaskLoopSimdDirectiveClass ||
>            T->getStmtClass() == OMPDistributeDirectiveClass ||
>            T->getStmtClass() == OMPTargetParallelForDirectiveClass ||
>            T->getStmtClass() == OMPDistributeParallelForDirectiveClass ||
>            T->getStmtClass() == OMPDistributeParallelForSimdDirectiveClass ||
>            T->getStmtClass() == OMPDistributeSimdDirectiveClass ||
>            T->getStmtClass() == OMPTargetParallelForSimdDirectiveClass ||
>            T->getStmtClass() == OMPTargetSimdDirectiveClass ||
>            T->getStmtClass() == OMPTeamsDistributeDirectiveClass ||
>            T->getStmtClass() == OMPTeamsDistributeSimdDirectiveClass ||
983,984c983,984
<                ACCTeamsDistributeParallelForSimdDirectiveClass ||
<            T->getStmtClass() == ACCTeamsDistributeParallelForDirectiveClass ||
---
>                OMPTeamsDistributeParallelForSimdDirectiveClass ||
>            T->getStmtClass() == OMPTeamsDistributeParallelForDirectiveClass ||
986c986
<                ACCTargetTeamsDistributeParallelForDirectiveClass ||
---
>                OMPTargetTeamsDistributeParallelForDirectiveClass ||
988,990c988,990
<                ACCTargetTeamsDistributeParallelForSimdDirectiveClass ||
<            T->getStmtClass() == ACCTargetTeamsDistributeDirectiveClass ||
<            T->getStmtClass() == ACCTargetTeamsDistributeSimdDirectiveClass;
---
>                OMPTargetTeamsDistributeParallelForSimdDirectiveClass ||
>            T->getStmtClass() == OMPTargetTeamsDistributeDirectiveClass ||
>            T->getStmtClass() == OMPTargetTeamsDistributeSimdDirectiveClass;
994c994
< /// \brief This represents '#pragma acc simd' directive.
---
> /// \brief This represents '#pragma omp simd' directive.
997c997
< /// #pragma acc simd private(a,b) linear(i,j:s) reduction(+:c,d)
---
> /// #pragma omp simd private(a,b) linear(i,j:s) reduction(+:c,d)
999c999
< /// In this example directive '#pragma acc simd' has clauses 'private'
---
> /// In this example directive '#pragma omp simd' has clauses 'private'
1003c1003
< class ACCSimdDirective : public ACCLoopDirective {
---
> class OMPSimdDirective : public OMPLoopDirective {
1012c1012
<   ACCSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
1014c1014
<       : ACCLoopDirective(this, ACCSimdDirectiveClass, ACCD_simd, StartLoc,
---
>       : OMPLoopDirective(this, OMPSimdDirectiveClass, OMPD_simd, StartLoc,
1022,1023c1022,1023
<   explicit ACCSimdDirective(unsigned CollapsedNum, unsigned NumClauses)
<       : ACCLoopDirective(this, ACCSimdDirectiveClass, ACCD_simd,
---
>   explicit OMPSimdDirective(unsigned CollapsedNum, unsigned NumClauses)
>       : OMPLoopDirective(this, OMPSimdDirectiveClass, OMPD_simd,
1038c1038
<   static ACCSimdDirective *Create(const ASTContext &C, SourceLocation StartLoc,
---
>   static OMPSimdDirective *Create(const ASTContext &C, SourceLocation StartLoc,
1040c1040
<                                   ArrayRef<ACCClause *> Clauses,
---
>                                   ArrayRef<OMPClause *> Clauses,
1051c1051
<   static ACCSimdDirective *CreateEmpty(const ASTContext &C, unsigned NumClauses,
---
>   static OMPSimdDirective *CreateEmpty(const ASTContext &C, unsigned NumClauses,
1055c1055
<     return T->getStmtClass() == ACCSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPSimdDirectiveClass;
1059c1059
< /// \brief This represents '#pragma acc for' directive.
---
> /// \brief This represents '#pragma omp for' directive.
1062c1062
< /// #pragma acc for private(a,b) reduction(+:c,d)
---
> /// #pragma omp for private(a,b) reduction(+:c,d)
1064c1064
< /// In this example directive '#pragma acc for' has clauses 'private' with the
---
> /// In this example directive '#pragma omp for' has clauses 'private' with the
1068c1068
< class ACCForDirective : public ACCLoopDirective {
---
> class OMPForDirective : public OMPLoopDirective {
1081c1081
<   ACCForDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPForDirective(SourceLocation StartLoc, SourceLocation EndLoc,
1083c1083
<       : ACCLoopDirective(this, ACCForDirectiveClass, ACCD_for, StartLoc, EndLoc,
---
>       : OMPLoopDirective(this, OMPForDirectiveClass, OMPD_for, StartLoc, EndLoc,
1092,1093c1092,1093
<   explicit ACCForDirective(unsigned CollapsedNum, unsigned NumClauses)
<       : ACCLoopDirective(this, ACCForDirectiveClass, ACCD_for, SourceLocation(),
---
>   explicit OMPForDirective(unsigned CollapsedNum, unsigned NumClauses)
>       : OMPLoopDirective(this, OMPForDirectiveClass, OMPD_for, SourceLocation(),
1112c1112
<   static ACCForDirective *Create(const ASTContext &C, SourceLocation StartLoc,
---
>   static OMPForDirective *Create(const ASTContext &C, SourceLocation StartLoc,
1114c1114
<                                  ArrayRef<ACCClause *> Clauses,
---
>                                  ArrayRef<OMPClause *> Clauses,
1125c1125
<   static ACCForDirective *CreateEmpty(const ASTContext &C, unsigned NumClauses,
---
>   static OMPForDirective *CreateEmpty(const ASTContext &C, unsigned NumClauses,
1132c1132
<     return T->getStmtClass() == ACCForDirectiveClass;
---
>     return T->getStmtClass() == OMPForDirectiveClass;
1136c1136
< /// \brief This represents '#pragma acc for simd' directive.
---
> /// \brief This represents '#pragma omp for simd' directive.
1139c1139
< /// #pragma acc for simd private(a,b) linear(i,j:s) reduction(+:c,d)
---
> /// #pragma omp for simd private(a,b) linear(i,j:s) reduction(+:c,d)
1141c1141
< /// In this example directive '#pragma acc for simd' has clauses 'private'
---
> /// In this example directive '#pragma omp for simd' has clauses 'private'
1145c1145
< class ACCForSimdDirective : public ACCLoopDirective {
---
> class OMPForSimdDirective : public OMPLoopDirective {
1154c1154
<   ACCForSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPForSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
1156c1156
<       : ACCLoopDirective(this, ACCForSimdDirectiveClass, ACCD_for_simd,
---
>       : OMPLoopDirective(this, OMPForSimdDirectiveClass, OMPD_for_simd,
1164,1165c1164,1165
<   explicit ACCForSimdDirective(unsigned CollapsedNum, unsigned NumClauses)
<       : ACCLoopDirective(this, ACCForSimdDirectiveClass, ACCD_for_simd,
---
>   explicit OMPForSimdDirective(unsigned CollapsedNum, unsigned NumClauses)
>       : OMPLoopDirective(this, OMPForSimdDirectiveClass, OMPD_for_simd,
1180c1180
<   static ACCForSimdDirective *
---
>   static OMPForSimdDirective *
1182c1182
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
1192c1192
<   static ACCForSimdDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPForSimdDirective *CreateEmpty(const ASTContext &C,
1197c1197
<     return T->getStmtClass() == ACCForSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPForSimdDirectiveClass;
1201c1201
< /// \brief This represents '#pragma acc sections' directive.
---
> /// \brief This represents '#pragma omp sections' directive.
1204c1204
< /// #pragma acc sections private(a,b) reduction(+:c,d)
---
> /// #pragma omp sections private(a,b) reduction(+:c,d)
1206c1206
< /// In this example directive '#pragma acc sections' has clauses 'private' with
---
> /// In this example directive '#pragma omp sections' has clauses 'private' with
1210c1210
< class ACCSectionsDirective : public ACCExecutableDirective {
---
> class OMPSectionsDirective : public OMPExecutableDirective {
1222c1222
<   ACCSectionsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPSectionsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
1224c1224
<       : ACCExecutableDirective(this, ACCSectionsDirectiveClass, ACCD_sections,
---
>       : OMPExecutableDirective(this, OMPSectionsDirectiveClass, OMPD_sections,
1232,1233c1232,1233
<   explicit ACCSectionsDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCSectionsDirectiveClass, ACCD_sections,
---
>   explicit OMPSectionsDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPSectionsDirectiveClass, OMPD_sections,
1251c1251
<   static ACCSectionsDirective *
---
>   static OMPSectionsDirective *
1253c1253
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel);
1261c1261
<   static ACCSectionsDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPSectionsDirective *CreateEmpty(const ASTContext &C,
1268c1268
<     return T->getStmtClass() == ACCSectionsDirectiveClass;
---
>     return T->getStmtClass() == OMPSectionsDirectiveClass;
1272c1272
< /// \brief This represents '#pragma acc section' directive.
---
> /// \brief This represents '#pragma omp section' directive.
1275c1275
< /// #pragma acc section
---
> /// #pragma omp section
1278c1278
< class ACCSectionDirective : public ACCExecutableDirective {
---
> class OMPSectionDirective : public OMPExecutableDirective {
1289,1290c1289,1290
<   ACCSectionDirective(SourceLocation StartLoc, SourceLocation EndLoc)
<       : ACCExecutableDirective(this, ACCSectionDirectiveClass, ACCD_section,
---
>   OMPSectionDirective(SourceLocation StartLoc, SourceLocation EndLoc)
>       : OMPExecutableDirective(this, OMPSectionDirectiveClass, OMPD_section,
1296,1297c1296,1297
<   explicit ACCSectionDirective()
<       : ACCExecutableDirective(this, ACCSectionDirectiveClass, ACCD_section,
---
>   explicit OMPSectionDirective()
>       : OMPExecutableDirective(this, OMPSectionDirectiveClass, OMPD_section,
1310c1310
<   static ACCSectionDirective *Create(const ASTContext &C,
---
>   static OMPSectionDirective *Create(const ASTContext &C,
1319c1319
<   static ACCSectionDirective *CreateEmpty(const ASTContext &C, EmptyShell);
---
>   static OMPSectionDirective *CreateEmpty(const ASTContext &C, EmptyShell);
1328c1328
<     return T->getStmtClass() == ACCSectionDirectiveClass;
---
>     return T->getStmtClass() == OMPSectionDirectiveClass;
1332c1332
< /// \brief This represents '#pragma acc single' directive.
---
> /// \brief This represents '#pragma omp single' directive.
1335c1335
< /// #pragma acc single private(a,b) copyprivate(c,d)
---
> /// #pragma omp single private(a,b) copyprivate(c,d)
1337c1337
< /// In this example directive '#pragma acc single' has clauses 'private' with
---
> /// In this example directive '#pragma omp single' has clauses 'private' with
1340c1340
< class ACCSingleDirective : public ACCExecutableDirective {
---
> class OMPSingleDirective : public OMPExecutableDirective {
1348c1348
<   ACCSingleDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPSingleDirective(SourceLocation StartLoc, SourceLocation EndLoc,
1350c1350
<       : ACCExecutableDirective(this, ACCSingleDirectiveClass, ACCD_single,
---
>       : OMPExecutableDirective(this, OMPSingleDirectiveClass, OMPD_single,
1357,1358c1357,1358
<   explicit ACCSingleDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCSingleDirectiveClass, ACCD_single,
---
>   explicit OMPSingleDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPSingleDirectiveClass, OMPD_single,
1371c1371
<   static ACCSingleDirective *
---
>   static OMPSingleDirective *
1373c1373
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt);
1381c1381
<   static ACCSingleDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPSingleDirective *CreateEmpty(const ASTContext &C,
1385c1385
<     return T->getStmtClass() == ACCSingleDirectiveClass;
---
>     return T->getStmtClass() == OMPSingleDirectiveClass;
1389c1389
< /// \brief This represents '#pragma acc master' directive.
---
> /// \brief This represents '#pragma omp master' directive.
1392c1392
< /// #pragma acc master
---
> /// #pragma omp master
1395c1395
< class ACCMasterDirective : public ACCExecutableDirective {
---
> class OMPMasterDirective : public OMPExecutableDirective {
1402,1403c1402,1403
<   ACCMasterDirective(SourceLocation StartLoc, SourceLocation EndLoc)
<       : ACCExecutableDirective(this, ACCMasterDirectiveClass, ACCD_master,
---
>   OMPMasterDirective(SourceLocation StartLoc, SourceLocation EndLoc)
>       : OMPExecutableDirective(this, OMPMasterDirectiveClass, OMPD_master,
1408,1409c1408,1409
<   explicit ACCMasterDirective()
<       : ACCExecutableDirective(this, ACCMasterDirectiveClass, ACCD_master,
---
>   explicit OMPMasterDirective()
>       : OMPExecutableDirective(this, OMPMasterDirectiveClass, OMPD_master,
1420c1420
<   static ACCMasterDirective *Create(const ASTContext &C,
---
>   static OMPMasterDirective *Create(const ASTContext &C,
1429c1429
<   static ACCMasterDirective *CreateEmpty(const ASTContext &C, EmptyShell);
---
>   static OMPMasterDirective *CreateEmpty(const ASTContext &C, EmptyShell);
1432c1432
<     return T->getStmtClass() == ACCMasterDirectiveClass;
---
>     return T->getStmtClass() == OMPMasterDirectiveClass;
1436c1436
< /// \brief This represents '#pragma acc critical' directive.
---
> /// \brief This represents '#pragma omp critical' directive.
1439c1439
< /// #pragma acc critical
---
> /// #pragma omp critical
1442c1442
< class ACCCriticalDirective : public ACCExecutableDirective {
---
> class OMPCriticalDirective : public OMPExecutableDirective {
1453c1453
<   ACCCriticalDirective(const DeclarationNameInfo &Name, SourceLocation StartLoc,
---
>   OMPCriticalDirective(const DeclarationNameInfo &Name, SourceLocation StartLoc,
1455c1455
<       : ACCExecutableDirective(this, ACCCriticalDirectiveClass, ACCD_critical,
---
>       : OMPExecutableDirective(this, OMPCriticalDirectiveClass, OMPD_critical,
1463,1464c1463,1464
<   explicit ACCCriticalDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCCriticalDirectiveClass, ACCD_critical,
---
>   explicit OMPCriticalDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPCriticalDirectiveClass, OMPD_critical,
1485c1485
<   static ACCCriticalDirective *
---
>   static OMPCriticalDirective *
1488c1488
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt);
1495c1495
<   static ACCCriticalDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPCriticalDirective *CreateEmpty(const ASTContext &C,
1503c1503
<     return T->getStmtClass() == ACCCriticalDirectiveClass;
---
>     return T->getStmtClass() == OMPCriticalDirectiveClass;
1507c1507
< /// \brief This represents '#pragma acc parallel for' directive.
---
> /// \brief This represents '#pragma omp parallel for' directive.
1510c1510
< /// #pragma acc parallel for private(a,b) reduction(+:c,d)
---
> /// #pragma omp parallel for private(a,b) reduction(+:c,d)
1512c1512
< /// In this example directive '#pragma acc parallel for' has clauses 'private'
---
> /// In this example directive '#pragma omp parallel for' has clauses 'private'
1516c1516
< class ACCParallelForDirective : public ACCLoopDirective {
---
> class OMPParallelForDirective : public OMPLoopDirective {
1529c1529
<   ACCParallelForDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPParallelForDirective(SourceLocation StartLoc, SourceLocation EndLoc,
1531c1531
<       : ACCLoopDirective(this, ACCParallelForDirectiveClass, ACCD_parallel_for,
---
>       : OMPLoopDirective(this, OMPParallelForDirectiveClass, OMPD_parallel_for,
1540,1541c1540,1541
<   explicit ACCParallelForDirective(unsigned CollapsedNum, unsigned NumClauses)
<       : ACCLoopDirective(this, ACCParallelForDirectiveClass, ACCD_parallel_for,
---
>   explicit OMPParallelForDirective(unsigned CollapsedNum, unsigned NumClauses)
>       : OMPLoopDirective(this, OMPParallelForDirectiveClass, OMPD_parallel_for,
1561c1561
<   static ACCParallelForDirective *
---
>   static OMPParallelForDirective *
1563c1563
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
1573c1573
<   static ACCParallelForDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPParallelForDirective *CreateEmpty(const ASTContext &C,
1582c1582
<     return T->getStmtClass() == ACCParallelForDirectiveClass;
---
>     return T->getStmtClass() == OMPParallelForDirectiveClass;
1586c1586
< /// \brief This represents '#pragma acc parallel for simd' directive.
---
> /// \brief This represents '#pragma omp parallel for simd' directive.
1589c1589
< /// #pragma acc parallel for simd private(a,b) linear(i,j:s) reduction(+:c,d)
---
> /// #pragma omp parallel for simd private(a,b) linear(i,j:s) reduction(+:c,d)
1591c1591
< /// In this example directive '#pragma acc parallel for simd' has clauses
---
> /// In this example directive '#pragma omp parallel for simd' has clauses
1596c1596
< class ACCParallelForSimdDirective : public ACCLoopDirective {
---
> class OMPParallelForSimdDirective : public OMPLoopDirective {
1605c1605
<   ACCParallelForSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPParallelForSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
1607,1608c1607,1608
<       : ACCLoopDirective(this, ACCParallelForSimdDirectiveClass,
<                          ACCD_parallel_for_simd, StartLoc, EndLoc, CollapsedNum,
---
>       : OMPLoopDirective(this, OMPParallelForSimdDirectiveClass,
>                          OMPD_parallel_for_simd, StartLoc, EndLoc, CollapsedNum,
1616c1616
<   explicit ACCParallelForSimdDirective(unsigned CollapsedNum,
---
>   explicit OMPParallelForSimdDirective(unsigned CollapsedNum,
1618,1619c1618,1619
<       : ACCLoopDirective(this, ACCParallelForSimdDirectiveClass,
<                          ACCD_parallel_for_simd, SourceLocation(),
---
>       : OMPLoopDirective(this, OMPParallelForSimdDirectiveClass,
>                          OMPD_parallel_for_simd, SourceLocation(),
1633c1633
<   static ACCParallelForSimdDirective *
---
>   static OMPParallelForSimdDirective *
1635c1635
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
1645c1645
<   static ACCParallelForSimdDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPParallelForSimdDirective *CreateEmpty(const ASTContext &C,
1651c1651
<     return T->getStmtClass() == ACCParallelForSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPParallelForSimdDirectiveClass;
1655c1655
< /// \brief This represents '#pragma acc parallel sections' directive.
---
> /// \brief This represents '#pragma omp parallel sections' directive.
1658c1658
< /// #pragma acc parallel sections private(a,b) reduction(+:c,d)
---
> /// #pragma omp parallel sections private(a,b) reduction(+:c,d)
1660c1660
< /// In this example directive '#pragma acc parallel sections' has clauses
---
> /// In this example directive '#pragma omp parallel sections' has clauses
1664c1664
< class ACCParallelSectionsDirective : public ACCExecutableDirective {
---
> class OMPParallelSectionsDirective : public OMPExecutableDirective {
1676c1676
<   ACCParallelSectionsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPParallelSectionsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
1678,1679c1678,1679
<       : ACCExecutableDirective(this, ACCParallelSectionsDirectiveClass,
<                                ACCD_parallel_sections, StartLoc, EndLoc,
---
>       : OMPExecutableDirective(this, OMPParallelSectionsDirectiveClass,
>                                OMPD_parallel_sections, StartLoc, EndLoc,
1687,1689c1687,1689
<   explicit ACCParallelSectionsDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCParallelSectionsDirectiveClass,
<                                ACCD_parallel_sections, SourceLocation(),
---
>   explicit OMPParallelSectionsDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPParallelSectionsDirectiveClass,
>                                OMPD_parallel_sections, SourceLocation(),
1706c1706
<   static ACCParallelSectionsDirective *
---
>   static OMPParallelSectionsDirective *
1708c1708
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel);
1716c1716
<   static ACCParallelSectionsDirective *
---
>   static OMPParallelSectionsDirective *
1723c1723
<     return T->getStmtClass() == ACCParallelSectionsDirectiveClass;
---
>     return T->getStmtClass() == OMPParallelSectionsDirectiveClass;
1727c1727
< /// \brief This represents '#pragma acc task' directive.
---
> /// \brief This represents '#pragma omp task' directive.
1730c1730
< /// #pragma acc task private(a,b) final(d)
---
> /// #pragma omp task private(a,b) final(d)
1732c1732
< /// In this example directive '#pragma acc task' has clauses 'private' with the
---
> /// In this example directive '#pragma omp task' has clauses 'private' with the
1735c1735
< class ACCTaskDirective : public ACCExecutableDirective {
---
> class OMPTaskDirective : public OMPExecutableDirective {
1746c1746
<   ACCTaskDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTaskDirective(SourceLocation StartLoc, SourceLocation EndLoc,
1748c1748
<       : ACCExecutableDirective(this, ACCTaskDirectiveClass, ACCD_task, StartLoc,
---
>       : OMPExecutableDirective(this, OMPTaskDirectiveClass, OMPD_task, StartLoc,
1756,1757c1756,1757
<   explicit ACCTaskDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCTaskDirectiveClass, ACCD_task,
---
>   explicit OMPTaskDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPTaskDirectiveClass, OMPD_task,
1775c1775
<   static ACCTaskDirective *Create(const ASTContext &C, SourceLocation StartLoc,
---
>   static OMPTaskDirective *Create(const ASTContext &C, SourceLocation StartLoc,
1777c1777
<                                   ArrayRef<ACCClause *> Clauses,
---
>                                   ArrayRef<OMPClause *> Clauses,
1786c1786
<   static ACCTaskDirective *CreateEmpty(const ASTContext &C, unsigned NumClauses,
---
>   static OMPTaskDirective *CreateEmpty(const ASTContext &C, unsigned NumClauses,
1793c1793
<     return T->getStmtClass() == ACCTaskDirectiveClass;
---
>     return T->getStmtClass() == OMPTaskDirectiveClass;
1797c1797
< /// \brief This represents '#pragma acc taskyield' directive.
---
> /// \brief This represents '#pragma omp taskyield' directive.
1800c1800
< /// #pragma acc taskyield
---
> /// #pragma omp taskyield
1803c1803
< class ACCTaskyieldDirective : public ACCExecutableDirective {
---
> class OMPTaskyieldDirective : public OMPExecutableDirective {
1810,1811c1810,1811
<   ACCTaskyieldDirective(SourceLocation StartLoc, SourceLocation EndLoc)
<       : ACCExecutableDirective(this, ACCTaskyieldDirectiveClass, ACCD_taskyield,
---
>   OMPTaskyieldDirective(SourceLocation StartLoc, SourceLocation EndLoc)
>       : OMPExecutableDirective(this, OMPTaskyieldDirectiveClass, OMPD_taskyield,
1816,1817c1816,1817
<   explicit ACCTaskyieldDirective()
<       : ACCExecutableDirective(this, ACCTaskyieldDirectiveClass, ACCD_taskyield,
---
>   explicit OMPTaskyieldDirective()
>       : OMPExecutableDirective(this, OMPTaskyieldDirectiveClass, OMPD_taskyield,
1827c1827
<   static ACCTaskyieldDirective *
---
>   static OMPTaskyieldDirective *
1834c1834
<   static ACCTaskyieldDirective *CreateEmpty(const ASTContext &C, EmptyShell);
---
>   static OMPTaskyieldDirective *CreateEmpty(const ASTContext &C, EmptyShell);
1837c1837
<     return T->getStmtClass() == ACCTaskyieldDirectiveClass;
---
>     return T->getStmtClass() == OMPTaskyieldDirectiveClass;
1841c1841
< /// \brief This represents '#pragma acc barrier' directive.
---
> /// \brief This represents '#pragma omp barrier' directive.
1844c1844
< /// #pragma acc barrier
---
> /// #pragma omp barrier
1847c1847
< class ACCBarrierDirective : public ACCExecutableDirective {
---
> class OMPBarrierDirective : public OMPExecutableDirective {
1854,1855c1854,1855
<   ACCBarrierDirective(SourceLocation StartLoc, SourceLocation EndLoc)
<       : ACCExecutableDirective(this, ACCBarrierDirectiveClass, ACCD_barrier,
---
>   OMPBarrierDirective(SourceLocation StartLoc, SourceLocation EndLoc)
>       : OMPExecutableDirective(this, OMPBarrierDirectiveClass, OMPD_barrier,
1860,1861c1860,1861
<   explicit ACCBarrierDirective()
<       : ACCExecutableDirective(this, ACCBarrierDirectiveClass, ACCD_barrier,
---
>   explicit OMPBarrierDirective()
>       : OMPExecutableDirective(this, OMPBarrierDirectiveClass, OMPD_barrier,
1871c1871
<   static ACCBarrierDirective *
---
>   static OMPBarrierDirective *
1878c1878
<   static ACCBarrierDirective *CreateEmpty(const ASTContext &C, EmptyShell);
---
>   static OMPBarrierDirective *CreateEmpty(const ASTContext &C, EmptyShell);
1881c1881
<     return T->getStmtClass() == ACCBarrierDirectiveClass;
---
>     return T->getStmtClass() == OMPBarrierDirectiveClass;
1885c1885
< /// \brief This represents '#pragma acc taskwait' directive.
---
> /// \brief This represents '#pragma omp taskwait' directive.
1888c1888
< /// #pragma acc taskwait
---
> /// #pragma omp taskwait
1891c1891
< class ACCTaskwaitDirective : public ACCExecutableDirective {
---
> class OMPTaskwaitDirective : public OMPExecutableDirective {
1898,1899c1898,1899
<   ACCTaskwaitDirective(SourceLocation StartLoc, SourceLocation EndLoc)
<       : ACCExecutableDirective(this, ACCTaskwaitDirectiveClass, ACCD_taskwait,
---
>   OMPTaskwaitDirective(SourceLocation StartLoc, SourceLocation EndLoc)
>       : OMPExecutableDirective(this, OMPTaskwaitDirectiveClass, OMPD_taskwait,
1904,1905c1904,1905
<   explicit ACCTaskwaitDirective()
<       : ACCExecutableDirective(this, ACCTaskwaitDirectiveClass, ACCD_taskwait,
---
>   explicit OMPTaskwaitDirective()
>       : OMPExecutableDirective(this, OMPTaskwaitDirectiveClass, OMPD_taskwait,
1915c1915
<   static ACCTaskwaitDirective *
---
>   static OMPTaskwaitDirective *
1922c1922
<   static ACCTaskwaitDirective *CreateEmpty(const ASTContext &C, EmptyShell);
---
>   static OMPTaskwaitDirective *CreateEmpty(const ASTContext &C, EmptyShell);
1925c1925
<     return T->getStmtClass() == ACCTaskwaitDirectiveClass;
---
>     return T->getStmtClass() == OMPTaskwaitDirectiveClass;
1929c1929
< /// This represents '#pragma acc taskgroup' directive.
---
> /// This represents '#pragma omp taskgroup' directive.
1932c1932
< /// #pragma acc taskgroup
---
> /// #pragma omp taskgroup
1935c1935
< class ACCTaskgroupDirective : public ACCExecutableDirective {
---
> class OMPTaskgroupDirective : public OMPExecutableDirective {
1943c1943
<   ACCTaskgroupDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTaskgroupDirective(SourceLocation StartLoc, SourceLocation EndLoc,
1945c1945
<       : ACCExecutableDirective(this, ACCTaskgroupDirectiveClass, ACCD_taskgroup,
---
>       : OMPExecutableDirective(this, OMPTaskgroupDirectiveClass, OMPD_taskgroup,
1951,1952c1951,1952
<   explicit ACCTaskgroupDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCTaskgroupDirectiveClass, ACCD_taskgroup,
---
>   explicit OMPTaskgroupDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPTaskgroupDirectiveClass, OMPD_taskgroup,
1971c1971
<   static ACCTaskgroupDirective *
---
>   static OMPTaskgroupDirective *
1973c1973
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt,
1981c1981
<   static ACCTaskgroupDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTaskgroupDirective *CreateEmpty(const ASTContext &C,
1994c1994
<     return T->getStmtClass() == ACCTaskgroupDirectiveClass;
---
>     return T->getStmtClass() == OMPTaskgroupDirectiveClass;
1998c1998
< /// \brief This represents '#pragma acc flush' directive.
---
> /// \brief This represents '#pragma omp flush' directive.
2001c2001
< /// #pragma acc flush(a,b)
---
> /// #pragma omp flush(a,b)
2003c2003
< /// In this example directive '#pragma acc flush' has 2 arguments- variables 'a'
---
> /// In this example directive '#pragma omp flush' has 2 arguments- variables 'a'
2005c2005
< /// 'acc flush' directive does not have clauses but have an optional list of
---
> /// 'omp flush' directive does not have clauses but have an optional list of
2008c2008
< class ACCFlushDirective : public ACCExecutableDirective {
---
> class OMPFlushDirective : public OMPExecutableDirective {
2016c2016
<   ACCFlushDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPFlushDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2018c2018
<       : ACCExecutableDirective(this, ACCFlushDirectiveClass, ACCD_flush,
---
>       : OMPExecutableDirective(this, OMPFlushDirectiveClass, OMPD_flush,
2025,2026c2025,2026
<   explicit ACCFlushDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCFlushDirectiveClass, ACCD_flush,
---
>   explicit OMPFlushDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPFlushDirectiveClass, OMPD_flush,
2036c2036
<   /// \param Clauses List of clauses (only single ACCFlushClause clause is
---
>   /// \param Clauses List of clauses (only single OMPFlushClause clause is
2039c2039
<   static ACCFlushDirective *Create(const ASTContext &C, SourceLocation StartLoc,
---
>   static OMPFlushDirective *Create(const ASTContext &C, SourceLocation StartLoc,
2041c2041
<                                    ArrayRef<ACCClause *> Clauses);
---
>                                    ArrayRef<OMPClause *> Clauses);
2049c2049
<   static ACCFlushDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPFlushDirective *CreateEmpty(const ASTContext &C,
2053c2053
<     return T->getStmtClass() == ACCFlushDirectiveClass;
---
>     return T->getStmtClass() == OMPFlushDirectiveClass;
2057c2057
< /// \brief This represents '#pragma acc ordered' directive.
---
> /// \brief This represents '#pragma omp ordered' directive.
2060c2060
< /// #pragma acc ordered
---
> /// #pragma omp ordered
2063c2063
< class ACCOrderedDirective : public ACCExecutableDirective {
---
> class OMPOrderedDirective : public OMPExecutableDirective {
2071c2071
<   ACCOrderedDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPOrderedDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2073c2073
<       : ACCExecutableDirective(this, ACCOrderedDirectiveClass, ACCD_ordered,
---
>       : OMPExecutableDirective(this, OMPOrderedDirectiveClass, OMPD_ordered,
2080,2081c2080,2081
<   explicit ACCOrderedDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCOrderedDirectiveClass, ACCD_ordered,
---
>   explicit OMPOrderedDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPOrderedDirectiveClass, OMPD_ordered,
2094c2094
<   static ACCOrderedDirective *
---
>   static OMPOrderedDirective *
2096c2096
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt);
2103c2103
<   static ACCOrderedDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPOrderedDirective *CreateEmpty(const ASTContext &C,
2107c2107
<     return T->getStmtClass() == ACCOrderedDirectiveClass;
---
>     return T->getStmtClass() == OMPOrderedDirectiveClass;
2111c2111
< /// \brief This represents '#pragma acc atomic' directive.
---
> /// \brief This represents '#pragma omp atomic' directive.
2114c2114
< /// #pragma acc atomic capture
---
> /// #pragma omp atomic capture
2116c2116
< /// In this example directive '#pragma acc atomic' has clause 'capture'.
---
> /// In this example directive '#pragma omp atomic' has clause 'capture'.
2118c2118
< class ACCAtomicDirective : public ACCExecutableDirective {
---
> class OMPAtomicDirective : public OMPExecutableDirective {
2146c2146
<   ACCAtomicDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPAtomicDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2148c2148
<       : ACCExecutableDirective(this, ACCAtomicDirectiveClass, ACCD_atomic,
---
>       : OMPExecutableDirective(this, OMPAtomicDirectiveClass, OMPD_atomic,
2156,2157c2156,2157
<   explicit ACCAtomicDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCAtomicDirectiveClass, ACCD_atomic,
---
>   explicit OMPAtomicDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPAtomicDirectiveClass, OMPD_atomic,
2193c2193
<   static ACCAtomicDirective *
---
>   static OMPAtomicDirective *
2195c2195
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, Expr *X, Expr *V,
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt, Expr *X, Expr *V,
2204c2204
<   static ACCAtomicDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPAtomicDirective *CreateEmpty(const ASTContext &C,
2240c2240
<     return T->getStmtClass() == ACCAtomicDirectiveClass;
---
>     return T->getStmtClass() == OMPAtomicDirectiveClass;
2244c2244
< /// \brief This represents '#pragma acc target' directive.
---
> /// \brief This represents '#pragma omp target' directive.
2247c2247
< /// #pragma acc target if(a)
---
> /// #pragma omp target if(a)
2249c2249
< /// In this example directive '#pragma acc target' has clause 'if' with
---
> /// In this example directive '#pragma omp target' has clause 'if' with
2252c2252
< class ACCTargetDirective : public ACCExecutableDirective {
---
> class OMPTargetDirective : public OMPExecutableDirective {
2260c2260
<   ACCTargetDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTargetDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2262c2262
<       : ACCExecutableDirective(this, ACCTargetDirectiveClass, ACCD_target,
---
>       : OMPExecutableDirective(this, OMPTargetDirectiveClass, OMPD_target,
2269,2270c2269,2270
<   explicit ACCTargetDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCTargetDirectiveClass, ACCD_target,
---
>   explicit OMPTargetDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPTargetDirectiveClass, OMPD_target,
2283c2283
<   static ACCTargetDirective *
---
>   static OMPTargetDirective *
2285c2285
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt);
2293c2293
<   static ACCTargetDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTargetDirective *CreateEmpty(const ASTContext &C,
2297c2297
<     return T->getStmtClass() == ACCTargetDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetDirectiveClass;
2301c2301
< /// \brief This represents '#pragma acc target data' directive.
---
> /// \brief This represents '#pragma omp target data' directive.
2304c2304
< /// #pragma acc target data device(0) if(a) map(b[:])
---
> /// #pragma omp target data device(0) if(a) map(b[:])
2306c2306
< /// In this example directive '#pragma acc target data' has clauses 'device'
---
> /// In this example directive '#pragma omp target data' has clauses 'device'
2310c2310
< class ACCTargetDataDirective : public ACCExecutableDirective {
---
> class OMPTargetDataDirective : public OMPExecutableDirective {
2318c2318
<   ACCTargetDataDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTargetDataDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2320,2321c2320,2321
<       : ACCExecutableDirective(this, ACCTargetDataDirectiveClass, 
<                                ACCD_target_data, StartLoc, EndLoc, NumClauses,
---
>       : OMPExecutableDirective(this, OMPTargetDataDirectiveClass, 
>                                OMPD_target_data, StartLoc, EndLoc, NumClauses,
2328,2330c2328,2330
<   explicit ACCTargetDataDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCTargetDataDirectiveClass, 
<                                ACCD_target_data, SourceLocation(),
---
>   explicit OMPTargetDataDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPTargetDataDirectiveClass, 
>                                OMPD_target_data, SourceLocation(),
2342c2342
<   static ACCTargetDataDirective *
---
>   static OMPTargetDataDirective *
2344c2344
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt);
2351c2351
<   static ACCTargetDataDirective *CreateEmpty(const ASTContext &C, unsigned N,
---
>   static OMPTargetDataDirective *CreateEmpty(const ASTContext &C, unsigned N,
2355c2355
<     return T->getStmtClass() == ACCTargetDataDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetDataDirectiveClass;
2359c2359
< /// \brief This represents '#pragma acc target enter data' directive.
---
> /// \brief This represents '#pragma omp target enter data' directive.
2362c2362
< /// #pragma acc target enter data device(0) if(a) map(b[:])
---
> /// #pragma omp target enter data device(0) if(a) map(b[:])
2364c2364
< /// In this example directive '#pragma acc target enter data' has clauses
---
> /// In this example directive '#pragma omp target enter data' has clauses
2368c2368
< class ACCTargetEnterDataDirective : public ACCExecutableDirective {
---
> class OMPTargetEnterDataDirective : public OMPExecutableDirective {
2376c2376
<   ACCTargetEnterDataDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTargetEnterDataDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2378,2379c2378,2379
<       : ACCExecutableDirective(this, ACCTargetEnterDataDirectiveClass,
<                                ACCD_target_enter_data, StartLoc, EndLoc,
---
>       : OMPExecutableDirective(this, OMPTargetEnterDataDirectiveClass,
>                                OMPD_target_enter_data, StartLoc, EndLoc,
2386,2388c2386,2388
<   explicit ACCTargetEnterDataDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCTargetEnterDataDirectiveClass,
<                                ACCD_target_enter_data, SourceLocation(),
---
>   explicit OMPTargetEnterDataDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPTargetEnterDataDirectiveClass,
>                                OMPD_target_enter_data, SourceLocation(),
2401c2401
<   static ACCTargetEnterDataDirective *
---
>   static OMPTargetEnterDataDirective *
2403c2403
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt);
2410c2410
<   static ACCTargetEnterDataDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTargetEnterDataDirective *CreateEmpty(const ASTContext &C,
2414c2414
<     return T->getStmtClass() == ACCTargetEnterDataDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetEnterDataDirectiveClass;
2418c2418
< /// \brief This represents '#pragma acc target exit data' directive.
---
> /// \brief This represents '#pragma omp target exit data' directive.
2421c2421
< /// #pragma acc target exit data device(0) if(a) map(b[:])
---
> /// #pragma omp target exit data device(0) if(a) map(b[:])
2423c2423
< /// In this example directive '#pragma acc target exit data' has clauses
---
> /// In this example directive '#pragma omp target exit data' has clauses
2427c2427
< class ACCTargetExitDataDirective : public ACCExecutableDirective {
---
> class OMPTargetExitDataDirective : public OMPExecutableDirective {
2435c2435
<   ACCTargetExitDataDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTargetExitDataDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2437,2438c2437,2438
<       : ACCExecutableDirective(this, ACCTargetExitDataDirectiveClass,
<                                ACCD_target_exit_data, StartLoc, EndLoc,
---
>       : OMPExecutableDirective(this, OMPTargetExitDataDirectiveClass,
>                                OMPD_target_exit_data, StartLoc, EndLoc,
2445,2447c2445,2447
<   explicit ACCTargetExitDataDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCTargetExitDataDirectiveClass,
<                                ACCD_target_exit_data, SourceLocation(),
---
>   explicit OMPTargetExitDataDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPTargetExitDataDirectiveClass,
>                                OMPD_target_exit_data, SourceLocation(),
2460c2460
<   static ACCTargetExitDataDirective *
---
>   static OMPTargetExitDataDirective *
2462c2462
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt);
2469c2469
<   static ACCTargetExitDataDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTargetExitDataDirective *CreateEmpty(const ASTContext &C,
2473c2473
<     return T->getStmtClass() == ACCTargetExitDataDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetExitDataDirectiveClass;
2477c2477
< /// \brief This represents '#pragma acc target parallel' directive.
---
> /// \brief This represents '#pragma omp target parallel' directive.
2480c2480
< /// #pragma acc target parallel if(a)
---
> /// #pragma omp target parallel if(a)
2482c2482
< /// In this example directive '#pragma acc target parallel' has clause 'if' with
---
> /// In this example directive '#pragma omp target parallel' has clause 'if' with
2485c2485
< class ACCTargetParallelDirective : public ACCExecutableDirective {
---
> class OMPTargetParallelDirective : public OMPExecutableDirective {
2493c2493
<   ACCTargetParallelDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTargetParallelDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2495,2496c2495,2496
<       : ACCExecutableDirective(this, ACCTargetParallelDirectiveClass,
<                                ACCD_target_parallel, StartLoc, EndLoc,
---
>       : OMPExecutableDirective(this, OMPTargetParallelDirectiveClass,
>                                OMPD_target_parallel, StartLoc, EndLoc,
2503,2505c2503,2505
<   explicit ACCTargetParallelDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCTargetParallelDirectiveClass,
<                                ACCD_target_parallel, SourceLocation(),
---
>   explicit OMPTargetParallelDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPTargetParallelDirectiveClass,
>                                OMPD_target_parallel, SourceLocation(),
2518c2518
<   static ACCTargetParallelDirective *
---
>   static OMPTargetParallelDirective *
2520c2520
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt);
2528c2528
<   static ACCTargetParallelDirective *
---
>   static OMPTargetParallelDirective *
2532c2532
<     return T->getStmtClass() == ACCTargetParallelDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetParallelDirectiveClass;
2536c2536
< /// \brief This represents '#pragma acc target parallel for' directive.
---
> /// \brief This represents '#pragma omp target parallel for' directive.
2539c2539
< /// #pragma acc target parallel for private(a,b) reduction(+:c,d)
---
> /// #pragma omp target parallel for private(a,b) reduction(+:c,d)
2541c2541
< /// In this example directive '#pragma acc target parallel for' has clauses
---
> /// In this example directive '#pragma omp target parallel for' has clauses
2545c2545
< class ACCTargetParallelForDirective : public ACCLoopDirective {
---
> class OMPTargetParallelForDirective : public OMPLoopDirective {
2558c2558
<   ACCTargetParallelForDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTargetParallelForDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2560,2561c2560,2561
<       : ACCLoopDirective(this, ACCTargetParallelForDirectiveClass,
<                          ACCD_target_parallel_for, StartLoc, EndLoc,
---
>       : OMPLoopDirective(this, OMPTargetParallelForDirectiveClass,
>                          OMPD_target_parallel_for, StartLoc, EndLoc,
2570c2570
<   explicit ACCTargetParallelForDirective(unsigned CollapsedNum,
---
>   explicit OMPTargetParallelForDirective(unsigned CollapsedNum,
2572,2573c2572,2573
<       : ACCLoopDirective(this, ACCTargetParallelForDirectiveClass,
<                          ACCD_target_parallel_for, SourceLocation(),
---
>       : OMPLoopDirective(this, OMPTargetParallelForDirectiveClass,
>                          OMPD_target_parallel_for, SourceLocation(),
2592c2592
<   static ACCTargetParallelForDirective *
---
>   static OMPTargetParallelForDirective *
2594c2594
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
2604c2604
<   static ACCTargetParallelForDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTargetParallelForDirective *CreateEmpty(const ASTContext &C,
2613c2613
<     return T->getStmtClass() == ACCTargetParallelForDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetParallelForDirectiveClass;
2617c2617
< /// \brief This represents '#pragma acc teams' directive.
---
> /// \brief This represents '#pragma omp teams' directive.
2620c2620
< /// #pragma acc teams if(a)
---
> /// #pragma omp teams if(a)
2622c2622
< /// In this example directive '#pragma acc teams' has clause 'if' with
---
> /// In this example directive '#pragma omp teams' has clause 'if' with
2625c2625
< class ACCTeamsDirective : public ACCExecutableDirective {
---
> class OMPTeamsDirective : public OMPExecutableDirective {
2633c2633
<   ACCTeamsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTeamsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2635c2635
<       : ACCExecutableDirective(this, ACCTeamsDirectiveClass, ACCD_teams,
---
>       : OMPExecutableDirective(this, OMPTeamsDirectiveClass, OMPD_teams,
2642,2643c2642,2643
<   explicit ACCTeamsDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCTeamsDirectiveClass, ACCD_teams,
---
>   explicit OMPTeamsDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPTeamsDirectiveClass, OMPD_teams,
2656c2656
<   static ACCTeamsDirective *Create(const ASTContext &C, SourceLocation StartLoc,
---
>   static OMPTeamsDirective *Create(const ASTContext &C, SourceLocation StartLoc,
2658c2658
<                                    ArrayRef<ACCClause *> Clauses,
---
>                                    ArrayRef<OMPClause *> Clauses,
2667c2667
<   static ACCTeamsDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTeamsDirective *CreateEmpty(const ASTContext &C,
2671c2671
<     return T->getStmtClass() == ACCTeamsDirectiveClass;
---
>     return T->getStmtClass() == OMPTeamsDirectiveClass;
2675c2675
< /// \brief This represents '#pragma acc cancellation point' directive.
---
> /// \brief This represents '#pragma omp cancellation point' directive.
2678c2678
< /// #pragma acc cancellation point for
---
> /// #pragma omp cancellation point for
2682c2682
< class ACCCancellationPointDirective : public ACCExecutableDirective {
---
> class OMPCancellationPointDirective : public OMPExecutableDirective {
2684c2684
<   OpenACCDirectiveKind CancelRegion;
---
>   OpenMPDirectiveKind CancelRegion;
2690,2693c2690,2693
<   ACCCancellationPointDirective(SourceLocation StartLoc, SourceLocation EndLoc)
<       : ACCExecutableDirective(this, ACCCancellationPointDirectiveClass,
<                                ACCD_cancellation_point, StartLoc, EndLoc, 0, 0),
<         CancelRegion(ACCD_unknown) {}
---
>   OMPCancellationPointDirective(SourceLocation StartLoc, SourceLocation EndLoc)
>       : OMPExecutableDirective(this, OMPCancellationPointDirectiveClass,
>                                OMPD_cancellation_point, StartLoc, EndLoc, 0, 0),
>         CancelRegion(OMPD_unknown) {}
2697,2699c2697,2699
<   explicit ACCCancellationPointDirective()
<       : ACCExecutableDirective(this, ACCCancellationPointDirectiveClass,
<                                ACCD_cancellation_point, SourceLocation(),
---
>   explicit OMPCancellationPointDirective()
>       : OMPExecutableDirective(this, OMPCancellationPointDirectiveClass,
>                                OMPD_cancellation_point, SourceLocation(),
2701c2701
<         CancelRegion(ACCD_unknown) {}
---
>         CancelRegion(OMPD_unknown) {}
2705c2705
<   void setCancelRegion(OpenACCDirectiveKind CR) { CancelRegion = CR; }
---
>   void setCancelRegion(OpenMPDirectiveKind CR) { CancelRegion = CR; }
2714c2714
<   static ACCCancellationPointDirective *
---
>   static OMPCancellationPointDirective *
2716c2716
<          OpenACCDirectiveKind CancelRegion);
---
>          OpenMPDirectiveKind CancelRegion);
2722c2722
<   static ACCCancellationPointDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPCancellationPointDirective *CreateEmpty(const ASTContext &C,
2726c2726
<   OpenACCDirectiveKind getCancelRegion() const { return CancelRegion; }
---
>   OpenMPDirectiveKind getCancelRegion() const { return CancelRegion; }
2729c2729
<     return T->getStmtClass() == ACCCancellationPointDirectiveClass;
---
>     return T->getStmtClass() == OMPCancellationPointDirectiveClass;
2733c2733
< /// \brief This represents '#pragma acc cancel' directive.
---
> /// \brief This represents '#pragma omp cancel' directive.
2736c2736
< /// #pragma acc cancel for
---
> /// #pragma omp cancel for
2740c2740
< class ACCCancelDirective : public ACCExecutableDirective {
---
> class OMPCancelDirective : public OMPExecutableDirective {
2742c2742
<   OpenACCDirectiveKind CancelRegion;
---
>   OpenMPDirectiveKind CancelRegion;
2749c2749
<   ACCCancelDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPCancelDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2751c2751
<       : ACCExecutableDirective(this, ACCCancelDirectiveClass, ACCD_cancel,
---
>       : OMPExecutableDirective(this, OMPCancelDirectiveClass, OMPD_cancel,
2753c2753
<         CancelRegion(ACCD_unknown) {}
---
>         CancelRegion(OMPD_unknown) {}
2758,2759c2758,2759
<   explicit ACCCancelDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCCancelDirectiveClass, ACCD_cancel,
---
>   explicit OMPCancelDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPCancelDirectiveClass, OMPD_cancel,
2762c2762
<         CancelRegion(ACCD_unknown) {}
---
>         CancelRegion(OMPD_unknown) {}
2766c2766
<   void setCancelRegion(OpenACCDirectiveKind CR) { CancelRegion = CR; }
---
>   void setCancelRegion(OpenMPDirectiveKind CR) { CancelRegion = CR; }
2776c2776
<   static ACCCancelDirective *
---
>   static OMPCancelDirective *
2778c2778
<          ArrayRef<ACCClause *> Clauses, OpenACCDirectiveKind CancelRegion);
---
>          ArrayRef<OMPClause *> Clauses, OpenMPDirectiveKind CancelRegion);
2785c2785
<   static ACCCancelDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPCancelDirective *CreateEmpty(const ASTContext &C,
2789c2789
<   OpenACCDirectiveKind getCancelRegion() const { return CancelRegion; }
---
>   OpenMPDirectiveKind getCancelRegion() const { return CancelRegion; }
2792c2792
<     return T->getStmtClass() == ACCCancelDirectiveClass;
---
>     return T->getStmtClass() == OMPCancelDirectiveClass;
2796c2796
< /// \brief This represents '#pragma acc taskloop' directive.
---
> /// \brief This represents '#pragma omp taskloop' directive.
2799c2799
< /// #pragma acc taskloop private(a,b) grainsize(val) num_tasks(num)
---
> /// #pragma omp taskloop private(a,b) grainsize(val) num_tasks(num)
2801c2801
< /// In this example directive '#pragma acc taskloop' has clauses 'private'
---
> /// In this example directive '#pragma omp taskloop' has clauses 'private'
2805c2805
< class ACCTaskLoopDirective : public ACCLoopDirective {
---
> class OMPTaskLoopDirective : public OMPLoopDirective {
2814c2814
<   ACCTaskLoopDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTaskLoopDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2816c2816
<       : ACCLoopDirective(this, ACCTaskLoopDirectiveClass, ACCD_taskloop,
---
>       : OMPLoopDirective(this, OMPTaskLoopDirectiveClass, OMPD_taskloop,
2824,2825c2824,2825
<   explicit ACCTaskLoopDirective(unsigned CollapsedNum, unsigned NumClauses)
<       : ACCLoopDirective(this, ACCTaskLoopDirectiveClass, ACCD_taskloop,
---
>   explicit OMPTaskLoopDirective(unsigned CollapsedNum, unsigned NumClauses)
>       : OMPLoopDirective(this, OMPTaskLoopDirectiveClass, OMPD_taskloop,
2840c2840
<   static ACCTaskLoopDirective *
---
>   static OMPTaskLoopDirective *
2842c2842
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
2852c2852
<   static ACCTaskLoopDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTaskLoopDirective *CreateEmpty(const ASTContext &C,
2857c2857
<     return T->getStmtClass() == ACCTaskLoopDirectiveClass;
---
>     return T->getStmtClass() == OMPTaskLoopDirectiveClass;
2861c2861
< /// \brief This represents '#pragma acc taskloop simd' directive.
---
> /// \brief This represents '#pragma omp taskloop simd' directive.
2864c2864
< /// #pragma acc taskloop simd private(a,b) grainsize(val) num_tasks(num)
---
> /// #pragma omp taskloop simd private(a,b) grainsize(val) num_tasks(num)
2866c2866
< /// In this example directive '#pragma acc taskloop simd' has clauses 'private'
---
> /// In this example directive '#pragma omp taskloop simd' has clauses 'private'
2870c2870
< class ACCTaskLoopSimdDirective : public ACCLoopDirective {
---
> class OMPTaskLoopSimdDirective : public OMPLoopDirective {
2879c2879
<   ACCTaskLoopSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTaskLoopSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2881,2882c2881,2882
<       : ACCLoopDirective(this, ACCTaskLoopSimdDirectiveClass,
<                          ACCD_taskloop_simd, StartLoc, EndLoc, CollapsedNum,
---
>       : OMPLoopDirective(this, OMPTaskLoopSimdDirectiveClass,
>                          OMPD_taskloop_simd, StartLoc, EndLoc, CollapsedNum,
2890,2892c2890,2892
<   explicit ACCTaskLoopSimdDirective(unsigned CollapsedNum, unsigned NumClauses)
<       : ACCLoopDirective(this, ACCTaskLoopSimdDirectiveClass,
<                          ACCD_taskloop_simd, SourceLocation(), SourceLocation(),
---
>   explicit OMPTaskLoopSimdDirective(unsigned CollapsedNum, unsigned NumClauses)
>       : OMPLoopDirective(this, OMPTaskLoopSimdDirectiveClass,
>                          OMPD_taskloop_simd, SourceLocation(), SourceLocation(),
2906c2906
<   static ACCTaskLoopSimdDirective *
---
>   static OMPTaskLoopSimdDirective *
2908c2908
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
2918c2918
<   static ACCTaskLoopSimdDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTaskLoopSimdDirective *CreateEmpty(const ASTContext &C,
2924c2924
<     return T->getStmtClass() == ACCTaskLoopSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPTaskLoopSimdDirectiveClass;
2928c2928
< /// \brief This represents '#pragma acc distribute' directive.
---
> /// \brief This represents '#pragma omp distribute' directive.
2931c2931
< /// #pragma acc distribute private(a,b)
---
> /// #pragma omp distribute private(a,b)
2933c2933
< /// In this example directive '#pragma acc distribute' has clauses 'private'
---
> /// In this example directive '#pragma omp distribute' has clauses 'private'
2936c2936
< class ACCDistributeDirective : public ACCLoopDirective {
---
> class OMPDistributeDirective : public OMPLoopDirective {
2946c2946
<   ACCDistributeDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPDistributeDirective(SourceLocation StartLoc, SourceLocation EndLoc,
2948c2948
<       : ACCLoopDirective(this, ACCDistributeDirectiveClass, ACCD_distribute,
---
>       : OMPLoopDirective(this, OMPDistributeDirectiveClass, OMPD_distribute,
2957,2958c2957,2958
<   explicit ACCDistributeDirective(unsigned CollapsedNum, unsigned NumClauses)
<       : ACCLoopDirective(this, ACCDistributeDirectiveClass, ACCD_distribute,
---
>   explicit OMPDistributeDirective(unsigned CollapsedNum, unsigned NumClauses)
>       : OMPLoopDirective(this, OMPDistributeDirectiveClass, OMPD_distribute,
2974c2974
<   static ACCDistributeDirective *
---
>   static OMPDistributeDirective *
2976c2976
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
2986c2986
<   static ACCDistributeDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPDistributeDirective *CreateEmpty(const ASTContext &C,
2991c2991
<     return T->getStmtClass() == ACCDistributeDirectiveClass;
---
>     return T->getStmtClass() == OMPDistributeDirectiveClass;
2995c2995
< /// \brief This represents '#pragma acc target update' directive.
---
> /// \brief This represents '#pragma omp target update' directive.
2998c2998
< /// #pragma acc target update to(a) from(b) device(1)
---
> /// #pragma omp target update to(a) from(b) device(1)
3000c3000
< /// In this example directive '#pragma acc target update' has clause 'to' with
---
> /// In this example directive '#pragma omp target update' has clause 'to' with
3004c3004
< class ACCTargetUpdateDirective : public ACCExecutableDirective {
---
> class OMPTargetUpdateDirective : public OMPExecutableDirective {
3012c3012
<   ACCTargetUpdateDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTargetUpdateDirective(SourceLocation StartLoc, SourceLocation EndLoc,
3014,3015c3014,3015
<       : ACCExecutableDirective(this, ACCTargetUpdateDirectiveClass,
<                                ACCD_target_update, StartLoc, EndLoc, NumClauses,
---
>       : OMPExecutableDirective(this, OMPTargetUpdateDirectiveClass,
>                                OMPD_target_update, StartLoc, EndLoc, NumClauses,
3022,3024c3022,3024
<   explicit ACCTargetUpdateDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCTargetUpdateDirectiveClass,
<                                ACCD_target_update, SourceLocation(),
---
>   explicit OMPTargetUpdateDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPTargetUpdateDirectiveClass,
>                                OMPD_target_update, SourceLocation(),
3036c3036
<   static ACCTargetUpdateDirective *
---
>   static OMPTargetUpdateDirective *
3038c3038
<          ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);
---
>          ArrayRef<OMPClause *> Clauses, Stmt *AssociatedStmt);
3046c3046
<   static ACCTargetUpdateDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTargetUpdateDirective *CreateEmpty(const ASTContext &C,
3050c3050
<     return T->getStmtClass() == ACCTargetUpdateDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetUpdateDirectiveClass;
3054c3054
< /// \brief This represents '#pragma acc distribute parallel for' composite
---
> /// \brief This represents '#pragma omp distribute parallel for' composite
3058c3058
< /// #pragma acc distribute parallel for private(a,b)
---
> /// #pragma omp distribute parallel for private(a,b)
3060c3060
< /// In this example directive '#pragma acc distribute parallel for' has clause
---
> /// In this example directive '#pragma omp distribute parallel for' has clause
3063c3063
< class ACCDistributeParallelForDirective : public ACCLoopDirective {
---
> class OMPDistributeParallelForDirective : public OMPLoopDirective {
3075c3075
<   ACCDistributeParallelForDirective(SourceLocation StartLoc,
---
>   OMPDistributeParallelForDirective(SourceLocation StartLoc,
3078,3079c3078,3079
<       : ACCLoopDirective(this, ACCDistributeParallelForDirectiveClass,
<                          ACCD_distribute_parallel_for, StartLoc, EndLoc,
---
>       : OMPLoopDirective(this, OMPDistributeParallelForDirectiveClass,
>                          OMPD_distribute_parallel_for, StartLoc, EndLoc,
3087c3087
<   explicit ACCDistributeParallelForDirective(unsigned CollapsedNum,
---
>   explicit OMPDistributeParallelForDirective(unsigned CollapsedNum,
3089,3090c3089,3090
<       : ACCLoopDirective(this, ACCDistributeParallelForDirectiveClass,
<                          ACCD_distribute_parallel_for, SourceLocation(),
---
>       : OMPLoopDirective(this, OMPDistributeParallelForDirectiveClass,
>                          OMPD_distribute_parallel_for, SourceLocation(),
3109c3109
<   static ACCDistributeParallelForDirective *
---
>   static OMPDistributeParallelForDirective *
3111c3111
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3121c3121
<   static ACCDistributeParallelForDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPDistributeParallelForDirective *CreateEmpty(const ASTContext &C,
3130c3130
<     return T->getStmtClass() == ACCDistributeParallelForDirectiveClass;
---
>     return T->getStmtClass() == OMPDistributeParallelForDirectiveClass;
3134c3134
< /// This represents '#pragma acc distribute parallel for simd' composite
---
> /// This represents '#pragma omp distribute parallel for simd' composite
3138c3138
< /// #pragma acc distribute parallel for simd private(x)
---
> /// #pragma omp distribute parallel for simd private(x)
3140c3140
< /// In this example directive '#pragma acc distribute parallel for simd' has
---
> /// In this example directive '#pragma omp distribute parallel for simd' has
3143c3143
< class ACCDistributeParallelForSimdDirective final : public ACCLoopDirective {
---
> class OMPDistributeParallelForSimdDirective final : public OMPLoopDirective {
3153c3153
<   ACCDistributeParallelForSimdDirective(SourceLocation StartLoc,
---
>   OMPDistributeParallelForSimdDirective(SourceLocation StartLoc,
3157,3158c3157,3158
<       : ACCLoopDirective(this, ACCDistributeParallelForSimdDirectiveClass,
<                          ACCD_distribute_parallel_for_simd, StartLoc, 
---
>       : OMPLoopDirective(this, OMPDistributeParallelForSimdDirectiveClass,
>                          OMPD_distribute_parallel_for_simd, StartLoc, 
3166c3166
<   explicit ACCDistributeParallelForSimdDirective(unsigned CollapsedNum,
---
>   explicit OMPDistributeParallelForSimdDirective(unsigned CollapsedNum,
3168,3169c3168,3169
<       : ACCLoopDirective(this, ACCDistributeParallelForSimdDirectiveClass,
<                          ACCD_distribute_parallel_for_simd, 
---
>       : OMPLoopDirective(this, OMPDistributeParallelForSimdDirectiveClass,
>                          OMPD_distribute_parallel_for_simd, 
3184c3184
<   static ACCDistributeParallelForSimdDirective *Create(
---
>   static OMPDistributeParallelForSimdDirective *Create(
3186c3186
<       unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>       unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3195c3195
<   static ACCDistributeParallelForSimdDirective *CreateEmpty(
---
>   static OMPDistributeParallelForSimdDirective *CreateEmpty(
3200c3200
<     return T->getStmtClass() == ACCDistributeParallelForSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPDistributeParallelForSimdDirectiveClass;
3204c3204
< /// This represents '#pragma acc distribute simd' composite directive.
---
> /// This represents '#pragma omp distribute simd' composite directive.
3207c3207
< /// #pragma acc distribute simd private(x)
---
> /// #pragma omp distribute simd private(x)
3209c3209
< /// In this example directive '#pragma acc distribute simd' has clause
---
> /// In this example directive '#pragma omp distribute simd' has clause
3212c3212
< class ACCDistributeSimdDirective final : public ACCLoopDirective {
---
> class OMPDistributeSimdDirective final : public OMPLoopDirective {
3222c3222
<   ACCDistributeSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPDistributeSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
3224,3225c3224,3225
<       : ACCLoopDirective(this, ACCDistributeSimdDirectiveClass,
<                          ACCD_distribute_simd, StartLoc, EndLoc, CollapsedNum,
---
>       : OMPLoopDirective(this, OMPDistributeSimdDirectiveClass,
>                          OMPD_distribute_simd, StartLoc, EndLoc, CollapsedNum,
3233c3233
<   explicit ACCDistributeSimdDirective(unsigned CollapsedNum, 
---
>   explicit OMPDistributeSimdDirective(unsigned CollapsedNum, 
3235,3236c3235,3236
<       : ACCLoopDirective(this, ACCDistributeSimdDirectiveClass,
<                          ACCD_distribute_simd, SourceLocation(),
---
>       : OMPLoopDirective(this, OMPDistributeSimdDirectiveClass,
>                          OMPD_distribute_simd, SourceLocation(),
3250c3250
<   static ACCDistributeSimdDirective *
---
>   static OMPDistributeSimdDirective *
3252c3252
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3261c3261
<   static ACCDistributeSimdDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPDistributeSimdDirective *CreateEmpty(const ASTContext &C,
3267c3267
<     return T->getStmtClass() == ACCDistributeSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPDistributeSimdDirectiveClass;
3271c3271
< /// This represents '#pragma acc target parallel for simd' directive.
---
> /// This represents '#pragma omp target parallel for simd' directive.
3274c3274
< /// #pragma acc target parallel for simd private(a) map(b) safelen(c)
---
> /// #pragma omp target parallel for simd private(a) map(b) safelen(c)
3276c3276
< /// In this example directive '#pragma acc target parallel for simd' has clauses
---
> /// In this example directive '#pragma omp target parallel for simd' has clauses
3280c3280
< class ACCTargetParallelForSimdDirective final : public ACCLoopDirective {
---
> class OMPTargetParallelForSimdDirective final : public OMPLoopDirective {
3290c3290
<   ACCTargetParallelForSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTargetParallelForSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
3292,3293c3292,3293
<       : ACCLoopDirective(this, ACCTargetParallelForSimdDirectiveClass,
<                          ACCD_target_parallel_for_simd, StartLoc, EndLoc,
---
>       : OMPLoopDirective(this, OMPTargetParallelForSimdDirectiveClass,
>                          OMPD_target_parallel_for_simd, StartLoc, EndLoc,
3301c3301
<   explicit ACCTargetParallelForSimdDirective(unsigned CollapsedNum,
---
>   explicit OMPTargetParallelForSimdDirective(unsigned CollapsedNum,
3303,3304c3303,3304
<       : ACCLoopDirective(this, ACCTargetParallelForSimdDirectiveClass,
<                          ACCD_target_parallel_for_simd, SourceLocation(),
---
>       : OMPLoopDirective(this, OMPTargetParallelForSimdDirectiveClass,
>                          OMPD_target_parallel_for_simd, SourceLocation(),
3318c3318
<   static ACCTargetParallelForSimdDirective *
---
>   static OMPTargetParallelForSimdDirective *
3320c3320
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3329c3329
<   static ACCTargetParallelForSimdDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTargetParallelForSimdDirective *CreateEmpty(const ASTContext &C,
3335c3335
<     return T->getStmtClass() == ACCTargetParallelForSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetParallelForSimdDirectiveClass;
3339c3339
< /// This represents '#pragma acc target simd' directive.
---
> /// This represents '#pragma omp target simd' directive.
3342c3342
< /// #pragma acc target simd private(a) map(b) safelen(c)
---
> /// #pragma omp target simd private(a) map(b) safelen(c)
3344c3344
< /// In this example directive '#pragma acc target simd' has clauses 'private'
---
> /// In this example directive '#pragma omp target simd' has clauses 'private'
3348c3348
< class ACCTargetSimdDirective final : public ACCLoopDirective {
---
> class OMPTargetSimdDirective final : public OMPLoopDirective {
3358c3358
<   ACCTargetSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTargetSimdDirective(SourceLocation StartLoc, SourceLocation EndLoc,
3360,3361c3360,3361
<       : ACCLoopDirective(this, ACCTargetSimdDirectiveClass,
<                          ACCD_target_simd, StartLoc, EndLoc, CollapsedNum,
---
>       : OMPLoopDirective(this, OMPTargetSimdDirectiveClass,
>                          OMPD_target_simd, StartLoc, EndLoc, CollapsedNum,
3369,3370c3369,3370
<   explicit ACCTargetSimdDirective(unsigned CollapsedNum, unsigned NumClauses)
<       : ACCLoopDirective(this, ACCTargetSimdDirectiveClass, ACCD_target_simd, 
---
>   explicit OMPTargetSimdDirective(unsigned CollapsedNum, unsigned NumClauses)
>       : OMPLoopDirective(this, OMPTargetSimdDirectiveClass, OMPD_target_simd, 
3385c3385
<   static ACCTargetSimdDirective *
---
>   static OMPTargetSimdDirective *
3387c3387
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3396c3396
<   static ACCTargetSimdDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTargetSimdDirective *CreateEmpty(const ASTContext &C,
3402c3402
<     return T->getStmtClass() == ACCTargetSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetSimdDirectiveClass;
3406c3406
< /// This represents '#pragma acc teams distribute' directive.
---
> /// This represents '#pragma omp teams distribute' directive.
3409c3409
< /// #pragma acc teams distribute private(a,b)
---
> /// #pragma omp teams distribute private(a,b)
3411c3411
< /// In this example directive '#pragma acc teams distribute' has clauses
---
> /// In this example directive '#pragma omp teams distribute' has clauses
3414c3414
< class ACCTeamsDistributeDirective final : public ACCLoopDirective {
---
> class OMPTeamsDistributeDirective final : public OMPLoopDirective {
3424c3424
<   ACCTeamsDistributeDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTeamsDistributeDirective(SourceLocation StartLoc, SourceLocation EndLoc,
3426,3427c3426,3427
<       : ACCLoopDirective(this, ACCTeamsDistributeDirectiveClass, 
<                          ACCD_teams_distribute, StartLoc, EndLoc, 
---
>       : OMPLoopDirective(this, OMPTeamsDistributeDirectiveClass, 
>                          OMPD_teams_distribute, StartLoc, EndLoc, 
3435c3435
<   explicit ACCTeamsDistributeDirective(unsigned CollapsedNum,
---
>   explicit OMPTeamsDistributeDirective(unsigned CollapsedNum,
3437,3438c3437,3438
<       : ACCLoopDirective(this, ACCTeamsDistributeDirectiveClass,
<                          ACCD_teams_distribute, SourceLocation(),
---
>       : OMPLoopDirective(this, OMPTeamsDistributeDirectiveClass,
>                          OMPD_teams_distribute, SourceLocation(),
3452c3452
<   static ACCTeamsDistributeDirective *
---
>   static OMPTeamsDistributeDirective *
3454c3454
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3463c3463
<   static ACCTeamsDistributeDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTeamsDistributeDirective *CreateEmpty(const ASTContext &C,
3469c3469
<     return T->getStmtClass() == ACCTeamsDistributeDirectiveClass;
---
>     return T->getStmtClass() == OMPTeamsDistributeDirectiveClass;
3473c3473
< /// This represents '#pragma acc teams distribute simd'
---
> /// This represents '#pragma omp teams distribute simd'
3477c3477
< /// #pragma acc teams distribute simd private(a,b)
---
> /// #pragma omp teams distribute simd private(a,b)
3479c3479
< /// In this example directive '#pragma acc teams distribute simd'
---
> /// In this example directive '#pragma omp teams distribute simd'
3482c3482
< class ACCTeamsDistributeSimdDirective final : public ACCLoopDirective {
---
> class OMPTeamsDistributeSimdDirective final : public OMPLoopDirective {
3492c3492
<   ACCTeamsDistributeSimdDirective(SourceLocation StartLoc,
---
>   OMPTeamsDistributeSimdDirective(SourceLocation StartLoc,
3495,3496c3495,3496
<       : ACCLoopDirective(this, ACCTeamsDistributeSimdDirectiveClass,
<                          ACCD_teams_distribute_simd, StartLoc, EndLoc,
---
>       : OMPLoopDirective(this, OMPTeamsDistributeSimdDirectiveClass,
>                          OMPD_teams_distribute_simd, StartLoc, EndLoc,
3504c3504
<   explicit ACCTeamsDistributeSimdDirective(unsigned CollapsedNum,
---
>   explicit OMPTeamsDistributeSimdDirective(unsigned CollapsedNum,
3506,3507c3506,3507
<       : ACCLoopDirective(this, ACCTeamsDistributeSimdDirectiveClass,
<                          ACCD_teams_distribute_simd, SourceLocation(),
---
>       : OMPLoopDirective(this, OMPTeamsDistributeSimdDirectiveClass,
>                          OMPD_teams_distribute_simd, SourceLocation(),
3521c3521
<   static ACCTeamsDistributeSimdDirective *
---
>   static OMPTeamsDistributeSimdDirective *
3523c3523
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3533c3533
<   static ACCTeamsDistributeSimdDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTeamsDistributeSimdDirective *CreateEmpty(const ASTContext &C,
3539c3539
<     return T->getStmtClass() == ACCTeamsDistributeSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPTeamsDistributeSimdDirectiveClass;
3543c3543
< /// This represents '#pragma acc teams distribute parallel for simd' composite
---
> /// This represents '#pragma omp teams distribute parallel for simd' composite
3547c3547
< /// #pragma acc teams distribute parallel for simd private(x)
---
> /// #pragma omp teams distribute parallel for simd private(x)
3549c3549
< /// In this example directive '#pragma acc teams distribute parallel for simd'
---
> /// In this example directive '#pragma omp teams distribute parallel for simd'
3552,3553c3552,3553
< class ACCTeamsDistributeParallelForSimdDirective final
<     : public ACCLoopDirective {
---
> class OMPTeamsDistributeParallelForSimdDirective final
>     : public OMPLoopDirective {
3563c3563
<   ACCTeamsDistributeParallelForSimdDirective(SourceLocation StartLoc,
---
>   OMPTeamsDistributeParallelForSimdDirective(SourceLocation StartLoc,
3567,3568c3567,3568
<       : ACCLoopDirective(this, ACCTeamsDistributeParallelForSimdDirectiveClass,
<                          ACCD_teams_distribute_parallel_for_simd, StartLoc, 
---
>       : OMPLoopDirective(this, OMPTeamsDistributeParallelForSimdDirectiveClass,
>                          OMPD_teams_distribute_parallel_for_simd, StartLoc, 
3576c3576
<   explicit ACCTeamsDistributeParallelForSimdDirective(unsigned CollapsedNum,
---
>   explicit OMPTeamsDistributeParallelForSimdDirective(unsigned CollapsedNum,
3578,3579c3578,3579
<       : ACCLoopDirective(this, ACCTeamsDistributeParallelForSimdDirectiveClass,
<                          ACCD_teams_distribute_parallel_for_simd, 
---
>       : OMPLoopDirective(this, OMPTeamsDistributeParallelForSimdDirectiveClass,
>                          OMPD_teams_distribute_parallel_for_simd, 
3594c3594
<   static ACCTeamsDistributeParallelForSimdDirective *
---
>   static OMPTeamsDistributeParallelForSimdDirective *
3596c3596
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3605c3605
<   static ACCTeamsDistributeParallelForSimdDirective *
---
>   static OMPTeamsDistributeParallelForSimdDirective *
3610c3610
<     return T->getStmtClass() == ACCTeamsDistributeParallelForSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPTeamsDistributeParallelForSimdDirectiveClass;
3614c3614
< /// This represents '#pragma acc teams distribute parallel for' composite
---
> /// This represents '#pragma omp teams distribute parallel for' composite
3618c3618
< /// #pragma acc teams distribute parallel for private(x)
---
> /// #pragma omp teams distribute parallel for private(x)
3620c3620
< /// In this example directive '#pragma acc teams distribute parallel for'
---
> /// In this example directive '#pragma omp teams distribute parallel for'
3623c3623
< class ACCTeamsDistributeParallelForDirective final : public ACCLoopDirective {
---
> class OMPTeamsDistributeParallelForDirective final : public OMPLoopDirective {
3635c3635
<   ACCTeamsDistributeParallelForDirective(SourceLocation StartLoc,
---
>   OMPTeamsDistributeParallelForDirective(SourceLocation StartLoc,
3639,3640c3639,3640
<       : ACCLoopDirective(this, ACCTeamsDistributeParallelForDirectiveClass,
<                          ACCD_teams_distribute_parallel_for, StartLoc, EndLoc,
---
>       : OMPLoopDirective(this, OMPTeamsDistributeParallelForDirectiveClass,
>                          OMPD_teams_distribute_parallel_for, StartLoc, EndLoc,
3648c3648
<   explicit ACCTeamsDistributeParallelForDirective(unsigned CollapsedNum,
---
>   explicit OMPTeamsDistributeParallelForDirective(unsigned CollapsedNum,
3650,3651c3650,3651
<       : ACCLoopDirective(this, ACCTeamsDistributeParallelForDirectiveClass,
<                          ACCD_teams_distribute_parallel_for, SourceLocation(),
---
>       : OMPLoopDirective(this, OMPTeamsDistributeParallelForDirectiveClass,
>                          OMPD_teams_distribute_parallel_for, SourceLocation(),
3670c3670
<   static ACCTeamsDistributeParallelForDirective *
---
>   static OMPTeamsDistributeParallelForDirective *
3672c3672
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3681c3681
<   static ACCTeamsDistributeParallelForDirective *
---
>   static OMPTeamsDistributeParallelForDirective *
3689c3689
<     return T->getStmtClass() == ACCTeamsDistributeParallelForDirectiveClass;
---
>     return T->getStmtClass() == OMPTeamsDistributeParallelForDirectiveClass;
3693c3693
< /// This represents '#pragma acc target teams' directive.
---
> /// This represents '#pragma omp target teams' directive.
3696c3696
< /// #pragma acc target teams if(a>0)
---
> /// #pragma omp target teams if(a>0)
3698c3698
< /// In this example directive '#pragma acc target teams' has clause 'if' with
---
> /// In this example directive '#pragma omp target teams' has clause 'if' with
3701c3701
< class ACCTargetTeamsDirective final : public ACCExecutableDirective {
---
> class OMPTargetTeamsDirective final : public OMPExecutableDirective {
3709c3709
<   ACCTargetTeamsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
---
>   OMPTargetTeamsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
3711,3712c3711,3712
<       : ACCExecutableDirective(this, ACCTargetTeamsDirectiveClass,
<                                ACCD_target_teams, StartLoc, EndLoc, NumClauses,
---
>       : OMPExecutableDirective(this, OMPTargetTeamsDirectiveClass,
>                                OMPD_target_teams, StartLoc, EndLoc, NumClauses,
3719,3721c3719,3721
<   explicit ACCTargetTeamsDirective(unsigned NumClauses)
<       : ACCExecutableDirective(this, ACCTargetTeamsDirectiveClass,
<                                ACCD_target_teams, SourceLocation(),
---
>   explicit OMPTargetTeamsDirective(unsigned NumClauses)
>       : OMPExecutableDirective(this, OMPTargetTeamsDirectiveClass,
>                                OMPD_target_teams, SourceLocation(),
3733c3733
<   static ACCTargetTeamsDirective *Create(const ASTContext &C,
---
>   static OMPTargetTeamsDirective *Create(const ASTContext &C,
3736c3736
<                                          ArrayRef<ACCClause *> Clauses,
---
>                                          ArrayRef<OMPClause *> Clauses,
3744c3744
<   static ACCTargetTeamsDirective *CreateEmpty(const ASTContext &C,
---
>   static OMPTargetTeamsDirective *CreateEmpty(const ASTContext &C,
3748c3748
<     return T->getStmtClass() == ACCTargetTeamsDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetTeamsDirectiveClass;
3752c3752
< /// This represents '#pragma acc target teams distribute' combined directive.
---
> /// This represents '#pragma omp target teams distribute' combined directive.
3755c3755
< /// #pragma acc target teams distribute private(x)
---
> /// #pragma omp target teams distribute private(x)
3757c3757
< /// In this example directive '#pragma acc target teams distribute' has clause
---
> /// In this example directive '#pragma omp target teams distribute' has clause
3760c3760
< class ACCTargetTeamsDistributeDirective final : public ACCLoopDirective {
---
> class OMPTargetTeamsDistributeDirective final : public OMPLoopDirective {
3770c3770
<   ACCTargetTeamsDistributeDirective(SourceLocation StartLoc,
---
>   OMPTargetTeamsDistributeDirective(SourceLocation StartLoc,
3773,3774c3773,3774
<       : ACCLoopDirective(this, ACCTargetTeamsDistributeDirectiveClass,
<                          ACCD_target_teams_distribute, StartLoc, EndLoc,
---
>       : OMPLoopDirective(this, OMPTargetTeamsDistributeDirectiveClass,
>                          OMPD_target_teams_distribute, StartLoc, EndLoc,
3782c3782
<   explicit ACCTargetTeamsDistributeDirective(unsigned CollapsedNum,
---
>   explicit OMPTargetTeamsDistributeDirective(unsigned CollapsedNum,
3784,3785c3784,3785
<       : ACCLoopDirective(this, ACCTargetTeamsDistributeDirectiveClass,
<                          ACCD_target_teams_distribute, SourceLocation(),
---
>       : OMPLoopDirective(this, OMPTargetTeamsDistributeDirectiveClass,
>                          OMPD_target_teams_distribute, SourceLocation(),
3799c3799
<   static ACCTargetTeamsDistributeDirective *
---
>   static OMPTargetTeamsDistributeDirective *
3801c3801
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3810c3810
<   static ACCTargetTeamsDistributeDirective *
---
>   static OMPTargetTeamsDistributeDirective *
3815c3815
<     return T->getStmtClass() == ACCTargetTeamsDistributeDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetTeamsDistributeDirectiveClass;
3819c3819
< /// This represents '#pragma acc target teams distribute parallel for' combined
---
> /// This represents '#pragma omp target teams distribute parallel for' combined
3823c3823
< /// #pragma acc target teams distribute parallel for private(x)
---
> /// #pragma omp target teams distribute parallel for private(x)
3825c3825
< /// In this example directive '#pragma acc target teams distribute parallel
---
> /// In this example directive '#pragma omp target teams distribute parallel
3828,3829c3828,3829
< class ACCTargetTeamsDistributeParallelForDirective final
<     : public ACCLoopDirective {
---
> class OMPTargetTeamsDistributeParallelForDirective final
>     : public OMPLoopDirective {
3841c3841
<   ACCTargetTeamsDistributeParallelForDirective(SourceLocation StartLoc,
---
>   OMPTargetTeamsDistributeParallelForDirective(SourceLocation StartLoc,
3845,3847c3845,3847
<       : ACCLoopDirective(this,
<                          ACCTargetTeamsDistributeParallelForDirectiveClass,
<                          ACCD_target_teams_distribute_parallel_for, StartLoc,
---
>       : OMPLoopDirective(this,
>                          OMPTargetTeamsDistributeParallelForDirectiveClass,
>                          OMPD_target_teams_distribute_parallel_for, StartLoc,
3856c3856
<   explicit ACCTargetTeamsDistributeParallelForDirective(unsigned CollapsedNum,
---
>   explicit OMPTargetTeamsDistributeParallelForDirective(unsigned CollapsedNum,
3858,3860c3858,3860
<       : ACCLoopDirective(
<             this, ACCTargetTeamsDistributeParallelForDirectiveClass,
<             ACCD_target_teams_distribute_parallel_for, SourceLocation(),
---
>       : OMPLoopDirective(
>             this, OMPTargetTeamsDistributeParallelForDirectiveClass,
>             OMPD_target_teams_distribute_parallel_for, SourceLocation(),
3879c3879
<   static ACCTargetTeamsDistributeParallelForDirective *
---
>   static OMPTargetTeamsDistributeParallelForDirective *
3881c3881
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3890c3890
<   static ACCTargetTeamsDistributeParallelForDirective *
---
>   static OMPTargetTeamsDistributeParallelForDirective *
3899c3899
<            ACCTargetTeamsDistributeParallelForDirectiveClass;
---
>            OMPTargetTeamsDistributeParallelForDirectiveClass;
3903c3903
< /// This represents '#pragma acc target teams distribute parallel for simd'
---
> /// This represents '#pragma omp target teams distribute parallel for simd'
3907c3907
< /// #pragma acc target teams distribute parallel for simd private(x)
---
> /// #pragma omp target teams distribute parallel for simd private(x)
3909c3909
< /// In this example directive '#pragma acc target teams distribute parallel
---
> /// In this example directive '#pragma omp target teams distribute parallel
3912,3913c3912,3913
< class ACCTargetTeamsDistributeParallelForSimdDirective final
<     : public ACCLoopDirective {
---
> class OMPTargetTeamsDistributeParallelForSimdDirective final
>     : public OMPLoopDirective {
3923c3923
<   ACCTargetTeamsDistributeParallelForSimdDirective(SourceLocation StartLoc,
---
>   OMPTargetTeamsDistributeParallelForSimdDirective(SourceLocation StartLoc,
3927,3929c3927,3929
<       : ACCLoopDirective(this,
<                          ACCTargetTeamsDistributeParallelForSimdDirectiveClass,
<                          ACCD_target_teams_distribute_parallel_for_simd,
---
>       : OMPLoopDirective(this,
>                          OMPTargetTeamsDistributeParallelForSimdDirectiveClass,
>                          OMPD_target_teams_distribute_parallel_for_simd,
3937c3937
<   explicit ACCTargetTeamsDistributeParallelForSimdDirective(
---
>   explicit OMPTargetTeamsDistributeParallelForSimdDirective(
3939,3941c3939,3941
<       : ACCLoopDirective(
<             this, ACCTargetTeamsDistributeParallelForSimdDirectiveClass,
<             ACCD_target_teams_distribute_parallel_for_simd, SourceLocation(),
---
>       : OMPLoopDirective(
>             this, OMPTargetTeamsDistributeParallelForSimdDirectiveClass,
>             OMPD_target_teams_distribute_parallel_for_simd, SourceLocation(),
3955c3955
<   static ACCTargetTeamsDistributeParallelForSimdDirective *
---
>   static OMPTargetTeamsDistributeParallelForSimdDirective *
3957c3957
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
3966c3966
<   static ACCTargetTeamsDistributeParallelForSimdDirective *
---
>   static OMPTargetTeamsDistributeParallelForSimdDirective *
3972c3972
<            ACCTargetTeamsDistributeParallelForSimdDirectiveClass;
---
>            OMPTargetTeamsDistributeParallelForSimdDirectiveClass;
3976c3976
< /// This represents '#pragma acc target teams distribute simd' combined
---
> /// This represents '#pragma omp target teams distribute simd' combined
3980c3980
< /// #pragma acc target teams distribute simd private(x)
---
> /// #pragma omp target teams distribute simd private(x)
3982c3982
< /// In this example directive '#pragma acc target teams distribute simd'
---
> /// In this example directive '#pragma omp target teams distribute simd'
3985c3985
< class ACCTargetTeamsDistributeSimdDirective final : public ACCLoopDirective {
---
> class OMPTargetTeamsDistributeSimdDirective final : public OMPLoopDirective {
3995c3995
<   ACCTargetTeamsDistributeSimdDirective(SourceLocation StartLoc,
---
>   OMPTargetTeamsDistributeSimdDirective(SourceLocation StartLoc,
3999,4000c3999,4000
<       : ACCLoopDirective(this, ACCTargetTeamsDistributeSimdDirectiveClass,
<                          ACCD_target_teams_distribute_simd, StartLoc, EndLoc,
---
>       : OMPLoopDirective(this, OMPTargetTeamsDistributeSimdDirectiveClass,
>                          OMPD_target_teams_distribute_simd, StartLoc, EndLoc,
4008c4008
<   explicit ACCTargetTeamsDistributeSimdDirective(unsigned CollapsedNum,
---
>   explicit OMPTargetTeamsDistributeSimdDirective(unsigned CollapsedNum,
4010,4011c4010,4011
<       : ACCLoopDirective(this, ACCTargetTeamsDistributeSimdDirectiveClass,
<                          ACCD_target_teams_distribute_simd, SourceLocation(),
---
>       : OMPLoopDirective(this, OMPTargetTeamsDistributeSimdDirectiveClass,
>                          OMPD_target_teams_distribute_simd, SourceLocation(),
4025c4025
<   static ACCTargetTeamsDistributeSimdDirective *
---
>   static OMPTargetTeamsDistributeSimdDirective *
4027c4027
<          unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
---
>          unsigned CollapsedNum, ArrayRef<OMPClause *> Clauses,
4036c4036
<   static ACCTargetTeamsDistributeSimdDirective *
---
>   static OMPTargetTeamsDistributeSimdDirective *
4041c4041
<     return T->getStmtClass() == ACCTargetTeamsDistributeSimdDirectiveClass;
---
>     return T->getStmtClass() == OMPTargetTeamsDistributeSimdDirectiveClass;
