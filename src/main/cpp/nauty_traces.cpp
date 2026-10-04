// Exact canonical labeling / automorphism orbits — JNI entry point backed by
// the real Traces() algorithm (Piperno), not nauty's classical
// individualization-refinement (densenauty()). Both live in the same
// vendored library (src/main/cpp/nauty, see COPYRIGHT there) and solve the
// same problem, but Traces generally out-performs nauty on graphs with large
// automorphism groups — exactly the case this scheme's designated-class /
// interface-coloring machinery is built to lean on, since it's the one that
// forces recursion into the expensive exact path in the first place.
//
// Traces operates on nauty's sparsegraph representation (v/d/e arrays — the
// same shape as our own CSR offsets/neighbors, so no format translation is
// needed beyond widening offsets to size_t) rather than the dense bitset
// `graph*` densenauty() uses. That's a second reason to prefer it here: the
// subinstances this scheme certifies are exactly the kind of moderate-size,
// often highly symmetric graphs (post color-refinement, post folding) where
// sparse representation and Traces' search strategy both pay off.
//
// What this shim returns, and why it's this shape (mirrors nauty_wl1.cpp /
// the previous densenauty()-based version):
//   - the canonical labeling itself (`lab`, in/out — Traces overwrites it)
//   - automorphism orbits (needed independently for Lemma 2 dedup upstream)
//   - search stats, packed as doubles. TracesStats has no `numbadleaves`
//     analogue (nauty's leaf-quality metric is specific to nauty's own
//     search strategy) — reported as 0, not a stand-in.
// This deliberately does NOT return canonical adjacency bytes: Kotlin already
// holds the original graph and rebuilds canonical adjacency directly from
// `lab` (canonical position i <-> original vertex lab[i]) without marshaling
// an n x n bit matrix across the JNI boundary. `canong` here is therefore a
// disposable scratch sparsegraph required by Traces()'s contract but never
// read back.
//
// Not thread-safe: Traces' own scratch workspace is static, shared across
// calls — serialize calls from the JVM side (see TracesJni.kt).

#include "nauty/traces.h"
#include "nauty/schreier.h"
#include <jni.h>
#include <vector>

namespace {

std::vector<int32_t> readIntArray(JNIEnv* env, jintArray arr) {
    jsize len = env->GetArrayLength(arr);
    std::vector<int32_t> buf(len);
    env->GetIntArrayRegion(arr, 0, len, buf.data());
    return buf;
}

// Scratch for Java_dialysis_cl_TracesJni_nativeGenerators: Traces' userautomproc callback has no
// user-data parameter (it's a bare C function pointer, `void(*)(int,int*,int)`), so the only way
// to get a found generator OUT of the callback is a global — safe here because, like the rest of
// this file, calls are already required to be serialized from the JVM side (Traces' own scratch
// workspace is static/shared too, see file doc), so there is never a second call's callback live
// at the same time as this one's.
std::vector<std::vector<int32_t>>* g_generatorSink = nullptr;

void collectGenerator(int /* count */, int* perm, int n) {
    if (g_generatorSink != nullptr) g_generatorSink->emplace_back(perm, perm + n);
}

}  // namespace

extern "C" {

JNIEXPORT jdoubleArray JNICALL Java_dialysis_cl_TracesJni_nativeCanon(
    JNIEnv* env, jobject,
    jintArray j_offsets, jintArray j_neighbors, jint maxVertex,
    jintArray j_lab0, jintArray j_ptn0,
    jintArray j_labOut, jintArray j_orbitsOut,
    jboolean j_getcanon) {
    int n = (int)maxVertex + 1;
    auto offsets = readIntArray(env, j_offsets);     // size n+1, offsets[n] == nde
    auto neighbors = readIntArray(env, j_neighbors);  // size nde
    auto lab = readIntArray(env, j_lab0);    // consumed as input, overwritten with the canonical labeling
    auto ptn = readIntArray(env, j_ptn0);    // consumed as scratch by Traces; never read back

    size_t nde = neighbors.size();

    SG_DECL(g);
    SG_ALLOC(g, n, nde, "nauty_traces malloc");
    g.nv = n;
    g.nde = nde;
    for (int v = 0; v < n; v++) {
        g.v[v] = (size_t)offsets[v];
        g.d[v] = offsets[v + 1] - offsets[v];
    }
    for (size_t i = 0; i < nde; i++) g.e[i] = neighbors[i];

    SG_DECL(canong);   // mandatory scratch for getcanon=TRUE; unread

    std::vector<int32_t> orbits(n);

    // Detect the trivial single-cell partition: lab == identity and ptn has no cell
    // boundary before the last position (exactly one cell spanning all n vertices — the
    // "uncolored" case, e.g. true-orbit measurement). Traces has a dedicated fast path for
    // exactly this case, gated by options.defaultptn (see traces.c: the `ti->regular` /
    // defaultptn branch skips the general partition-processing loop entirely) — the same
    // path dreadnaut uses whenever no partition command is given. Manually encoding an
    // equivalent one-cell partition and passing defaultptn=FALSE (the previous behavior)
    // takes the slow general-purpose path instead: measured ~12x slower (26.7s vs 2.2s)
    // on an uncolored 2808-vertex rigid-CFI instance. A genuinely colored (multi-cell)
    // partition must still set defaultptn=FALSE — that flag means "ignore whatever
    // partition you were given," which is only correct when it WAS the trivial one.
    bool isTrivialPartition = true;
    for (int i = 0; i < n && isTrivialPartition; i++) {
        if (lab[i] != i) isTrivialPartition = false;
        if (i < n - 1 && ptn[i] == 0) isTrivialPartition = false;
    }

    DEFAULTOPTIONS_TRACES(options);
    // getcanon=TRUE asks Traces to additionally PROVE canonicity (no other search branch
    // produces a smaller labeling) — real, often substantial extra search cost on top of
    // just finding the automorphism group/orbits. A caller that only wants orbits (e.g.
    // true-orbit measurement, never CanonicalLabeler.certificate/canonicalLabeling) should
    // pass getcanon=false: dreadnaut's own default (DEFAULTOPTIONS_TRACES has getcanon=FALSE)
    // is exactly this, which is why plain orbit/group queries there are so much cheaper than
    // this wrapper's previous always-TRUE behavior.
    options.getcanon = j_getcanon;
    options.defaultptn = isTrivialPartition ? TRUE : FALSE;

    TracesStats stats;
    Traces(&g, lab.data(), ptn.data(), orbits.data(), &options, &stats, &canong);

    env->SetIntArrayRegion(j_labOut, 0, n, lab.data());
    env->SetIntArrayRegion(j_orbitsOut, 0, n, orbits.data());

    SG_FREE(g);
    SG_FREE(canong);

    double statsOut[6] = {
        (double)stats.numnodes, 0.0 /* no badLeaves analogue in Traces */, (double)stats.numorbits,
        (double)stats.numgenerators, stats.grpsize1, (double)stats.grpsize2,
    };
    jdoubleArray result = env->NewDoubleArray(6);
    // Same null-after-allocation-failure check as paige_tarjan_wl1.cpp's newIntArray -- under heap
    // exhaustion this returns null with a pending OutOfMemoryError; skip the dereferencing
    // SetDoubleArrayRegion below and let that propagate cleanly instead of a native SIGSEGV.
    if (result == nullptr) return nullptr;
    env->SetDoubleArrayRegion(result, 0, 6, statsOut);
    return result;
}

// Aut(colored graph)'s GENERATORS (paper "piece-coset" scheme's `autgrp` — see PIECE_COSET_SPEC.md
// 0.4): unlike nativeCanon above (which only ever surfaced group ORDER via TracesStats, never the
// actual permutations), this collects every generator Traces finds via its own userautomproc
// callback (traces.h: the vendored library already supports this, just not previously wired to
// JNI) and returns them as one jintArray per generator, each of length n (a full permutation of
// [0,n), not just its support). getcanon is always FALSE here: this call only wants the
// automorphism group, never a proof of canonicity — same rationale as nativeCanon's own
// getcanon=false path (measured ~12x cheaper on an uncolored rigid-CFI instance).
JNIEXPORT jobjectArray JNICALL Java_dialysis_cl_TracesJni_nativeGenerators(
    JNIEnv* env, jobject,
    jintArray j_offsets, jintArray j_neighbors, jint maxVertex,
    jintArray j_lab0, jintArray j_ptn0) {
    int n = (int)maxVertex + 1;
    auto offsets = readIntArray(env, j_offsets);
    auto neighbors = readIntArray(env, j_neighbors);
    auto lab = readIntArray(env, j_lab0);
    auto ptn = readIntArray(env, j_ptn0);

    size_t nde = neighbors.size();

    SG_DECL(g);
    SG_ALLOC(g, n, nde, "nauty_traces malloc");
    g.nv = n;
    g.nde = nde;
    for (int v = 0; v < n; v++) {
        g.v[v] = (size_t)offsets[v];
        g.d[v] = offsets[v + 1] - offsets[v];
    }
    for (size_t i = 0; i < nde; i++) g.e[i] = neighbors[i];

    SG_DECL(canong);   // mandatory scratch even with getcanon=FALSE; unread

    bool isTrivialPartition = true;
    for (int i = 0; i < n && isTrivialPartition; i++) {
        if (lab[i] != i) isTrivialPartition = false;
        if (i < n - 1 && ptn[i] == 0) isTrivialPartition = false;
    }

    std::vector<int32_t> orbits(n);   // Traces requires this buffer; not returned here

    DEFAULTOPTIONS_TRACES(options);
    options.getcanon = FALSE;
    options.defaultptn = isTrivialPartition ? TRUE : FALSE;
    options.userautomproc = &collectGenerator;

    std::vector<std::vector<int32_t>> collected;
    g_generatorSink = &collected;

    TracesStats stats;
    Traces(&g, lab.data(), ptn.data(), orbits.data(), &options, &stats, &canong);

    g_generatorSink = nullptr;

    SG_FREE(g);
    SG_FREE(canong);

    jclass intArrayClass = env->FindClass("[I");
    jobjectArray result = env->NewObjectArray((jsize)collected.size(), intArrayClass, nullptr);
    // Same null-after-allocation-failure check as paige_tarjan_wl1.cpp's newIntArray, on both the
    // outer array and each per-generator array the loop below allocates -- under heap exhaustion
    // either can return null (with a pending OutOfMemoryError already thrown), and dereferencing it
    // in SetObjectArrayElement/SetIntArrayRegion is a native SIGSEGV instead of a clean propagation.
    if (result == nullptr) return nullptr;
    for (size_t i = 0; i < collected.size(); i++) {
        jintArray perm = env->NewIntArray(n);
        if (perm == nullptr) return nullptr;
        env->SetIntArrayRegion(perm, 0, n, collected[i].data());
        env->SetObjectArrayElement(result, (jsize)i, perm);
        env->DeleteLocalRef(perm);
    }
    return result;
}

// Exact group order from an ALREADY-KNOWN generator list, via nauty's own vendored Schreier-Sims
// (src/main/cpp/nauty/schreier.c) -- newgroup/addgenerator/grouporder, the identical sequence
// nauty.c and traces.c use internally to compute their own TracesStats.grpsize1/2 (see nauty.c's
// `doschreier` calls and traces.c's `grouporderplus`, both `newgroup(&gp,&gens,n)` then
// `addgenerator(&gp,&gens,workperm,n)` per found automorphism). This does NOT run Traces or nauty's
// own search at all -- the generators are supplied by the CALLER (e.g. dialysis's own SAT-oracle
// orbit-stabiliser chain, GROUP_DISCOVERY_SPEC.md Part B), and schreier.c's bookkeeping is
// generator-agnostic: it computes |<generators>| via a base-and-strong-generating-set construction
// regardless of where the generators came from. This replaces a capped brute-force enumeration of
// the whole group (dialysis.sat.cadical.groupOrderByEnumeration) with the same technique nauty uses
// for groups far too large to ever enumerate directly.
//
// TWO wrong attempts before this one, both worth recording since the fix isn't obvious from the
// header alone:
//
// (1) `grouporder(nullptr, 0, gp, &gens, ...)` -- nfix=0 does NOT mean "give me the whole group's
//     order". grouporder's own per-level loop only runs `nfix` times, and everything past that is
//     covered ONLY by a fallback factor (size of the LARGEST orbit at wherever the loop stopped --
//     meant for an INCOMPLETE base / point-stabiliser query). With nfix=0 that fires immediately
//     using gp's own top-level orbits: this returned "size of the largest orbit", not |G| --
//     confirmed directly, generators whose product should give order 6 or 8 came back as 3 or 4.
//
// (2) Walking `sh->fixed >= 0` across the WHOLE chain myself, without ever calling `getorbits` with
//     an explicit non-empty `fix[]` first -- also wrong, but for a more basic reason:
//     `addgenerator`/`filterschreier` do NOT establish new base levels on their own. Reading
//     filterschreier's own loop: when it reaches a level with `fixed < 0` (nothing established
//     yet), it just `break`s and records the permutation, unsifted, in the generator ring -- it
//     never creates a new level itself. Base construction is the CALLER's job, done via
//     `getorbits(fix[], nfix, ...)` with an explicit, chosen sequence of points (nauty.c's own
//     search picks this incrementally, tied to which vertices it individualizes) -- confirmed
//     directly: without that, `gp->fixed` stayed -1 even after several `addgenerator` calls, so the
//     walk above terminated immediately and always returned 1.0.
//
// The actual fix: since we have no search of our own driving base selection, and n here never
// exceeds a few thousand (this project's own instance sizes), just fix EVERY point in natural order
// as the base (`fix = [0, 1, ..., n-1]`) via `getorbits(fix, n, ...)` -- getorbits's own doc confirms
// this constructs any missing levels; the levels beyond the group's real "moved" support just end up
// with singleton orbits (a harmless factor of 1 each in grouporder's product). `expandschreier`
// (called once already inside getorbits, twice more here, matching how many times grouporder() itself
// calls it) sifts the known generators through the now-established chain via randomized filtering
// (schreierfails trials) to populate it correctly. Cost is O(n) schreier levels -- fine at this
// project's scale, but a caller with n in the tens of thousands or more should build a MINIMAL base
// instead (skip points whose orbit under the so-far-known stabiliser is already a singleton, the way
// dialysis.sat.cadical.discoverAutomorphismGroupChain's own base selection already does on the Kotlin
// side) rather than paying for n unnecessary levels.
JNIEXPORT jdoubleArray JNICALL Java_dialysis_cl_TracesJni_nativeGroupOrder(
    JNIEnv* env, jobject,
    jint n, jobjectArray j_generators) {
    schreier* gp = nullptr;
    permnode* gens = nullptr;
    newgroup(&gp, &gens, n);

    jsize numGens = env->GetArrayLength(j_generators);
    std::vector<int32_t> perm(n);
    for (jsize i = 0; i < numGens; i++) {
        jintArray g = (jintArray)env->GetObjectArrayElement(j_generators, i);
        env->GetIntArrayRegion(g, 0, n, perm.data());
        env->DeleteLocalRef(g);
        addgenerator(&gp, &gens, perm.data(), n);
    }

    std::vector<int32_t> fullBase(n);
    for (int i = 0; i < n; i++) fullBase[i] = i;
    getorbits(fullBase.data(), n, gp, &gens, n);
    expandschreier(gp, &gens, n);
    expandschreier(gp, &gens, n);

    double grpsize1;
    int grpsize2;
    grouporder(fullBase.data(), n, gp, &gens, &grpsize1, &grpsize2, n);

    freeschreier(&gp, &gens);

    double out[2] = {grpsize1, (double)grpsize2};
    jdoubleArray result = env->NewDoubleArray(2);
    if (result == nullptr) return nullptr;  // pending OutOfMemoryError -- let it propagate, see above
    env->SetDoubleArrayRegion(result, 0, 2, out);
    return result;
}

}  // extern "C"