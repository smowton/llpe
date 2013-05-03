// Implement a slight customisation of the usual postdominator tree:
// The tree is specific to a loop context: the backedge of the loop leads to an artificial "next iteration"
// node. This is because it gets used to determine whether blocks are certain in this iteration,
// whilst the usual postdom tree would say that any nodes heading towards the exit are inevitable
// because the loop will terminate eventually.

// The iterators are just modified versions of the usual versions in ADT/CFG.h.

#include "llvm/ADT/GraphTraits.h"
#include "llvm/Function.h"
#include "llvm/InstrTypes.h"

using namespace llvm;

namespace llvm {

// Use this godawful wrapper class to carry a map from BBs to Loops so that we can store
// <BB, Loop> pairs somewhere we can take addresses.

struct LoopWrapper;

struct BBWrapper {

  ShadowBBInvar* BB;
  const LoopWrapper* L;
  bool hideSuccessors;

BBWrapper(): BB(0), L(0) { }
BBWrapper(ShadowBBInvar* _BB, bool hide, const LoopWrapper* _L) : BB(_BB), L(_L), hideSuccessors(hide) { }
  
  BBWrapper* get(ShadowBBInvar* BB) const;

};

// Another wrapper, for a Loop, limiting scope to blocks within the loop, the immediate
// exit blocks and the dummy "next iteration header" node with no block.

struct LoopWrapper {

  ShadowFunctionInvar& F;
  ShadowLoopInvar* LInfo;
  const Loop* L;
  std::vector<BBWrapper*> BBs;

LoopWrapper(const Loop* _L, ShadowFunctionInvar& _F) : F(_F), L(_L) {

  if(L) {

    LInfo = F.LInfo[L];
    // Lowest BB index we need is the loop's header:
    
    uint32_t LowestIdx = LInfo->headerIdx;
    uint32_t HighestIdx = LInfo->headerIdx;

    while(HighestIdx < F.BBs.size() && L->contains(F.BBs[HighestIdx].naturalScope))
      ++HighestIdx;
      
    --HighestIdx;

    // These exit blocks must be topo > all blocks in the loop, so only consider them.
    for(std::vector<uint32_t>::iterator it = LInfo->exitBlocks.begin(), it2 = LInfo->exitBlocks.end(); it != it2; ++it) {  

      if(*it > HighestIdx)
	HighestIdx = *it;

    }

    release_assert(HighestIdx != (uint32_t)0);

    // One extra space for the dummy next iter node.
    BBs.resize((HighestIdx - LowestIdx) + 2);

    for(uint32_t i = LowestIdx; (i <= HighestIdx) && (L->contains(F.BBs[i].naturalScope)); ++i) {
      ShadowBBInvar* SBB = &(F.BBs[i]);
      BBs[SBB->idx - LowestIdx] = new BBWrapper(SBB, /* hide successors = */ false, this);
    }
  
    for(std::vector<uint32_t>::iterator it = LInfo->exitBlocks.begin(), it2 = LInfo->exitBlocks.end(); it != it2; ++it) {
      ShadowBBInvar* SBB = &(F.BBs[*it]);
      BBs[SBB->idx - LowestIdx] = new BBWrapper(SBB, /* hide successors = */ true, this);
    }
  
    BBs[BBs.size() - 1] = new BBWrapper(0, true, this);

  }
  else {

    // Not in a loop, no trickery required.
    LInfo = 0;

    BBs.resize(F.BBs.size());
    for(uint32_t i = 0, ilim = F.BBs.size(); i < ilim; ++i)
      BBs[i] = new BBWrapper(&(F.BBs[i]), false, this);

  }

}

  BBWrapper* get(const ShadowBBInvar* BB) const {

    // First case symbolises the dummy next iteration node, only applies to loops.
    if(!BB)
      return BBs[BBs.size() - 1];
    
    uint32_t Offset = LInfo ? LInfo->headerIdx : 0;
    if(BB->idx < Offset || (BB->idx - Offset) >= BBs.size())
      return 0;
    else
      return BBs[BB->idx - Offset];
    
  }

  const BBWrapper& front() const {

    return *(BBs[0]);

  }
  
  size_t size() const {

    return BBs.size();

  }

  struct iterator {

    std::vector<BBWrapper*>::const_iterator it;
    std::vector<BBWrapper*>::const_iterator itend;

  iterator(std::vector<BBWrapper*>::const_iterator _it, std::vector<BBWrapper*>::const_iterator _itend) : it(_it), itend(_itend) { }

    bool operator==(const iterator& x) const {
      return x.it == it;
    }
    bool operator!=(const iterator& x) const {
      return x.it != it;
    }
    iterator& operator++() {
      // Skip past gaps in the BBWrapper vector, if any.
      assert(it != itend && "Iterator out of range");
      do {
	it++;
      } while(it != itend && !*it);
      return *this;
    }
    operator const BBWrapper*() { return *it; }

  };
  
  iterator begin() const { return iterator(BBs.begin(), BBs.end()); }
  iterator end() const { return iterator(BBs.end(), BBs.end()); }

};

 BBWrapper* BBWrapper::get(ShadowBBInvar* BB) const {

  return L->get(BB);

}

template <class Ptr> // Predecessor Iterator
class LoopPredIterator : public std::iterator<std::forward_iterator_tag,
						Ptr, ptrdiff_t> {
  typedef std::iterator<std::forward_iterator_tag, Ptr, ptrdiff_t> super;
  typedef LoopPredIterator<Ptr> Self;
  Ptr* ThisBB;
  uint32_t nextPred;
  bool isNextIter;
  bool isEnd;

public:
  typedef typename super::pointer pointer;

  explicit inline LoopPredIterator(Ptr *bb) : ThisBB(bb) {
    if(bb->BB && ((!bb->L->L) || bb->BB->BB != bb->L->L->getHeader())) {
      isNextIter = false;
      nextPred = 0;
    }
    else {
      // This is the special next-iteration node
      isNextIter = true;
      isEnd = false;
    }
  }
  inline LoopPredIterator(Ptr *bb, bool) : ThisBB(bb) {
    if(bb->BB && ((!bb->L->L) || bb->BB->BB != bb->L->L->getHeader())) {
      isNextIter = false;
      nextPred = bb->BB->preds_size();
    }
    else {
      // This is the special next-iteration node
      isNextIter = true;
      isEnd = true;
    }
  }

  inline bool operator==(const Self& x) const { 

    if(!isNextIter)
      return nextPred == x.nextPred;
    else
      return isEnd == x.isEnd;

  }

  inline bool operator!=(const Self& x) const { return !operator==(x); }

  inline pointer operator*() const {
   
    pointer ret;

    if(!isNextIter) {
      assert(nextPred < ThisBB->BB->preds_size() && "pred_iterator out of range!");
      ret = ThisBB->get(ThisBB->BB->getPred(nextPred));
    }
    else {
      assert(!isEnd);
      ret = ThisBB->L->BBs[ThisBB->L->LInfo->latchIdx - ThisBB->L->LInfo->headerIdx];
    }

    release_assert(ret);
    return ret;

  }
  inline pointer *operator->() const { return &operator*(); }

  inline Self& operator++() {   // Preincrement
    if(!isNextIter) {
      assert(nextPred < ThisBB->BB->preds_size() && "pred_iterator out of range!");
      ++nextPred;
    }
    else {
      assert(!isEnd);
      isEnd = true;
    }
    return *this;
  }

  inline Self operator++(int) { // Postincrement
    Self tmp = *this; ++*this; return tmp;
  }
};

typedef LoopPredIterator<BBWrapper> loop_pred_iterator;
typedef LoopPredIterator<const BBWrapper> const_loop_pred_iterator;

inline loop_pred_iterator loop_pred_begin(BBWrapper* BB) { return loop_pred_iterator(BB); }
inline loop_pred_iterator loop_pred_end(BBWrapper *BB) { return loop_pred_iterator(BB, true); }

template <class BB_>           // Successor Iterator
class LoopSuccIterator : public std::iterator<std::bidirectional_iterator_tag,
                                          BB_, ptrdiff_t> {
  const BB_* Block;
  uint32_t idx;
  typedef std::iterator<std::bidirectional_iterator_tag, BB_, ptrdiff_t> super;
  typedef LoopSuccIterator<BB_> Self;

  inline bool index_is_valid(int idx) {
    if(!Block->BB)
      return idx == 0;
    else
      return idx >= 0 && idx < Block->succs_size();
  }

public:
  typedef typename super::pointer pointer;
  // TODO: This can be random access iterator, only operator[] missing.

  explicit inline LoopSuccIterator(BB_* B) : Block(B), idx(0) {} // begin iterator

  inline LoopSuccIterator(BB_* B, bool) : Block(B) {

    // We hide the successor nodes of the special next-iteration node and loop exit blocks.
    if(!B->hideSuccessors)
      idx = B->BB->succs_size();
    else
      idx = 0;

  }

  inline const Self &operator=(const Self &I) {
    assert(Block == I.Block && "Cannot assign iterators to two different blocks!");
    idx = I.idx;
    return *this;
  }

  /// getSuccessorIndex - This is used to interface between code that wants to
  /// operate on terminator instructions directly.
  unsigned getSuccessorIndex() const { return idx; }

  inline bool operator==(const Self& x) const { return idx == x.idx; }
  inline bool operator!=(const Self& x) const { return !operator==(x); }

  inline pointer operator*() const { 
    ShadowBBInvar* NextBB = Block->BB->getSucc(idx);
    // Loop latch's successor is not the loop header but the dummy next-iteration node.
    if(Block->L->L && NextBB->BB == Block->L->L->getHeader() && Block->BB->BB == Block->L->L->getLoopLatch())
      return Block->get(0);
    else
      return Block->get(NextBB);
  }
  inline pointer operator->() const { return operator*(); }

  inline Self& operator++() { ++idx; return *this; } // Preincrement

  inline Self operator++(int) { // Postincrement
    Self tmp = *this; ++*this; return tmp;
  }

  inline Self& operator--() { --idx; return *this; }  // Predecrement
  inline Self operator--(int) { // Postdecrement
    Self tmp = *this; --*this; return tmp;
  }

  inline bool operator<(const Self& x) const {
    assert(Term == x.Term && "Cannot compare iterators of different blocks!");
    return idx < x.idx;
  }

  inline bool operator<=(const Self& x) const {
    assert(Term == x.Term && "Cannot compare iterators of different blocks!");
    return idx <= x.idx;
  }
  inline bool operator>=(const Self& x) const {
    assert(Term == x.Term && "Cannot compare iterators of different blocks!");
    return idx >= x.idx;
  }

  inline bool operator>(const Self& x) const {
    assert(Term == x.Term && "Cannot compare iterators of different blocks!");
    return idx > x.idx;
  }

  inline Self& operator+=(int Right) {
    unsigned new_idx = idx + Right;
    assert(index_is_valid(new_idx) && "Iterator index out of bound");
    idx = new_idx;
    return *this;
  }

  inline Self operator+(int Right) {
    Self tmp = *this;
    tmp += Right;
    return tmp;
  }

  inline Self& operator-=(int Right) {
    return operator+=(-Right);
  }

  inline Self operator-(int Right) {
    return operator+(-Right);
  }

  inline int operator-(const Self& x) {
    assert(Block == x.Block && "Cannot work on iterators of different blocks!");
    int distance = idx - x.idx;
    return distance;
  }

  // This works for read access, however write access is difficult as changes
  // to Term are only possible with Term->setSuccessor(idx). Pointers that can
  // be modified are not available.
  //
  // inline pointer operator[](int offset) {
  //  Self tmp = *this;
  //  tmp += offset;
  //  return tmp.operator*();
  // }

  /// Get the source BB of this iterator.
  inline BB_ *getSource() {
    return Block;
  }
};

typedef LoopSuccIterator<BBWrapper> loop_succ_iterator;

inline loop_succ_iterator loop_succ_begin(BBWrapper* BB) {
  return loop_succ_iterator(BB);
}
inline loop_succ_iterator loop_succ_end(BBWrapper* BB) {
  return loop_succ_iterator(BB, true);
}

template <> struct GraphTraits<BBWrapper*> {
  typedef BBWrapper NodeType;
  typedef loop_succ_iterator ChildIteratorType;

  static NodeType *getEntryNode(NodeType *BB) { return BB; }
  static inline ChildIteratorType child_begin(NodeType *N) {
    return loop_succ_begin(N);
  }
  static inline ChildIteratorType child_end(NodeType *N) {
    return loop_succ_end(N);
  }
};

// Provide specializations of GraphTraits to be able to treat a function as a
// graph of basic blocks... and to walk it in inverse order.  Inverse order for
// a function is considered to be when traversing the predecessor edges of a BB
// instead of the successor edges.
//
template <> struct GraphTraits<Inverse<BBWrapper*> > {
  typedef BBWrapper NodeType;
  typedef loop_pred_iterator ChildIteratorType;
  static NodeType *getEntryNode(Inverse<BBWrapper*> G) { return G.Graph; }
  static inline ChildIteratorType child_begin(NodeType *N) {
    return loop_pred_begin(N);
  }
  static inline ChildIteratorType child_end(NodeType *N) {
    return loop_pred_end(N);
  }
};

// Silly iterator wrapper to provide an implicit conversion to BBWrapper*

 struct NodesItWrapper {

   std::vector<BBWrapper*>::const_iterator wrapped;
   typedef BBWrapper* convtype;

 NodesItWrapper(std::vector<BBWrapper*>::const_iterator x) : wrapped(x) { }

   operator convtype() {

     return *wrapped;

   }

   inline NodesItWrapper& operator++() { ++wrapped; return *this; } // Preincrement
   
 };

// Provide specializations of GraphTraits to be able to treat a function as a
// graph of basic blocks... these are the same as the basic block iterators,
// except that the root node is implicitly the first node of the function.
//
template <> struct GraphTraits<LoopWrapper*> :
  public GraphTraits<BBWrapper*> {
  static NodeType *getEntryNode(const LoopWrapper *LW) { 
    return LW->BBs.front();
  }

  // nodes_iterator/begin/end - Allow iteration over all nodes in the graph
  typedef NodesItWrapper nodes_iterator;
  static nodes_iterator nodes_begin(const LoopWrapper *LW) { return NodesItWrapper(LW->BBs.begin()); }
  static nodes_iterator nodes_end  (const LoopWrapper *LW) { return NodesItWrapper(LW->BBs.end()); }

  static unsigned size(LoopWrapper* LW) { return LW->BBs.size(); }

};


// Provide specializations of GraphTraits to be able to treat a function as a
// graph of basic blocks... and to walk it in inverse order.  Inverse order for
// a function is considered to be when traversing the predecessor edges of a BB
// instead of the successor edges.
//
template <> struct GraphTraits<Inverse<LoopWrapper*> > :
  public GraphTraits<Inverse<BBWrapper*> > {
  static NodeType *getEntryNode(Inverse<LoopWrapper*> G) {
    return G.Graph->BBs.front();
  }
};

} // End namespace llvm



