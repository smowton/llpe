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

struct BBWrapper {

  const BasicBlock* BB;
  const Loop* L;
  DenseMap<const BasicBlock*, BBWrapper>* Map;

BBWrapper(): BB(0), L(0), Map(0) { }
BBWrapper(const BasicBlock* _BB, const Loop* _L, DenseMap<const BasicBlock*, BBWrapper>* _Map) : BB(_BB), L(_L), Map(_Map) { }

  const BBWrapper* get(const BasicBlock* BB) const {

    DenseMap<const BasicBlock*, BBWrapper>::const_iterator it = Map->find(BB);
    if(it != Map->end())
      return &(it->second);
    else
      return 0;

  }

};

// Another wrapper, for a Loop, limiting scope to blocks within the loop, the immediate
// exit blocks and the dummy "next iteration header" node with no block.

struct LoopWrapper {

  const Loop* L;
  std::vector<const BBWrapper*> BBs;
  DenseMap<const BasicBlock*, BBWrapper> Map;

LoopWrapper(const Loop* _L) : L(_L) {

  for(Loop::block_iterator LI = L->block_begin(), LE = L->block_end(); LI != LE; ++LI) {
    Map[*LI] = BBWrapper(*LI, L, &Map);
  }

  SmallVector<BasicBlock*, 4> ExitBlocks;
  L->getExitBlocks(ExitBlocks);
  
  for(SmallVector<BasicBlock*, 4>::iterator it = ExitBlocks.begin(), it2 = ExitBlocks.end(); it != it2; ++it) {
    Map[*it] = BBWrapper(*it, L, &Map);
  }

  Map[0] = BBWrapper(0, L, &Map);

  for(DenseMap<const BasicBlock*, BBWrapper>::iterator MI = Map.begin(), ME = Map.end(); MI != ME; ++MI) {

    BBs.push_back(&(MI->second));

  }

}

  const BBWrapper* get(const BasicBlock* BB) const {

    DenseMap<const BasicBlock*, BBWrapper>::const_iterator it = Map.find(BB);
    if(it == Map.end())
      return 0;
    else
      return &(it->second);

  }

  const BBWrapper& front() const {

    return *get(L->getHeader());

  }
  
  size_t size() const {

    return BBs.size();

  }

  struct iterator {

    std::vector<const BBWrapper*>::const_iterator it;

  iterator(std::vector<const BBWrapper*>::const_iterator _it) : it(_it) { }

    bool operator==(const iterator& x) const {
      return x.it == it;
    }
    bool operator!=(const iterator& x) const {
      return x.it != it;
    }
    iterator& operator++() {
      it++;
      return *this;
    }
    operator const BBWrapper*() { return *it; }

  };
  
  iterator begin() const { return iterator(BBs.begin()); }
  iterator end() const { return iterator(BBs.end()); }

};

template <class Ptr, class USE_iterator> // Predecessor Iterator
class LoopPredIterator : public std::iterator<std::forward_iterator_tag,
						Ptr, ptrdiff_t> {
  typedef std::iterator<std::forward_iterator_tag, Ptr, ptrdiff_t> super;
  typedef LoopPredIterator<Ptr, USE_iterator> Self;
  Ptr* ThisBB;
  USE_iterator It;
  bool isNextIter;
  bool isEnd;

  inline bool shouldSkipUse(const User* U) {

    if(const TerminatorInst* TI = dyn_cast<TerminatorInst>(U)) {
      return ThisBB->L->getHeader() == TI->getParent();
    }
    else {
      return true;
    }
   
  }

  inline void advancePastNonTerminators() {
    // Loop to ignore non terminator uses (for example PHI nodes).
    while (!It.atEnd() && shouldSkipUse(*It))
      ++It;
  }

public:
  typedef typename super::pointer pointer;

  explicit inline LoopPredIterator(Ptr *bb) : ThisBB(bb), It() {
    if(bb->BB && bb->BB != bb->L->getHeader()) {
      isNextIter = false;
      It = USE_iterator(bb->BB->use_begin());
      advancePastNonTerminators();
    }
    else {
      isNextIter = true;
      isEnd = false;
    }
  }
  inline LoopPredIterator(Ptr *bb, bool) : ThisBB(bb), It() {
    if(bb->BB && bb->BB != bb->L->getHeader()) {
      isNextIter = false;
      It = USE_iterator(bb->BB->use_end());
    }
    else {
      isNextIter = true;
      isEnd = true;
    }
  }

  inline bool operator==(const Self& x) const { 

    if(!isNextIter)
      return It == x.It; 
    else
      return isEnd == x.isEnd;

  }

  inline bool operator!=(const Self& x) const { return !operator==(x); }

  inline pointer operator*() const {
   
    if(!isNextIter) {
      assert(!It.atEnd() && "pred_iterator out of range!");
      return ThisBB->get(cast<TerminatorInst>(*It)->getParent());
    }
    else {
      assert(!isEnd);
      return ThisBB->get(ThisBB->L->getLoopLatch());
    }

  }
  inline pointer *operator->() const { return &operator*(); }

  inline Self& operator++() {   // Preincrement
    if(!isNextIter) {
      assert(!It.atEnd() && "pred_iterator out of range!");
      ++It; advancePastNonTerminators();
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

typedef LoopPredIterator<BBWrapper, Value::use_iterator> loop_pred_iterator;
typedef LoopPredIterator<const BBWrapper,
			   Value::const_use_iterator> const_loop_pred_iterator;

inline const_loop_pred_iterator loop_pred_begin(const BBWrapper* BB) { return const_loop_pred_iterator(BB); }
inline const_loop_pred_iterator loop_pred_end(const BBWrapper *BB) { return const_loop_pred_iterator(BB, true); }

template <class Term_, class BB_>           // Successor Iterator
class LoopSuccIterator : public std::iterator<std::bidirectional_iterator_tag,
                                          BB_, ptrdiff_t> {
  const BB_* Block;
  Term_ Term;
  unsigned idx;
  typedef std::iterator<std::bidirectional_iterator_tag, BB_, ptrdiff_t> super;
  typedef LoopSuccIterator<Term_, BB_> Self;

  inline bool index_is_valid(int idx) {
    if(!Block->BB)
      return idx == 0;
    else
      return idx >= 0 && (unsigned) idx < Term->getNumSuccessors();
  }

public:
  typedef typename super::pointer pointer;
  // TODO: This can be random access iterator, only operator[] missing.

  explicit inline LoopSuccIterator(BB_* B) : Block(B), idx(0) {// begin iterator
    // Hide successors of exit blocks and the "next iteration" psuedo-node.
    if(B->BB && B->L->contains(B->BB))
      Term = B->BB->getTerminator();
    else
      Term = 0;
  }

  inline LoopSuccIterator(BB_* B, bool) : Block(B) {
    if(B->BB && B->L->contains(B->BB)) {
      Term = B->BB->getTerminator();
      idx = Term->getNumSuccessors();
    }
    else {
      Term = 0;
      idx = 0;
    }
  }

  inline const Self &operator=(const Self &I) {
    assert(Term == I.Term &&"Cannot assign iterators to two different blocks!");
    idx = I.idx;
    return *this;
  }

  /// getSuccessorIndex - This is used to interface between code that wants to
  /// operate on terminator instructions directly.
  unsigned getSuccessorIndex() const { return idx; }

  inline bool operator==(const Self& x) const { return idx == x.idx; }
  inline bool operator!=(const Self& x) const { return !operator==(x); }

  inline pointer operator*() const { 
    assert(Term && "Can't dereference dummy iterator!");
    const BasicBlock* NextBB = Term->getSuccessor(idx);
    if(NextBB == Block->L->getHeader() && Block->BB == Block->L->getLoopLatch())
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
    assert(Term == x.Term && "Cannot work on iterators of different blocks!");
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
    if(!Term)
      return 0;
    else
      return Block;
  }
};

typedef LoopSuccIterator<const TerminatorInst*, const BBWrapper> loop_succ_iterator;

inline loop_succ_iterator loop_succ_begin(const BBWrapper* BB) {
  return loop_succ_iterator(BB);
}
inline loop_succ_iterator loop_succ_end(const BBWrapper* BB) {
  return loop_succ_iterator(BB, true);
}

template <> struct GraphTraits<const BBWrapper*> {
  typedef const BBWrapper NodeType;
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
template <> struct GraphTraits<Inverse<const BBWrapper*> > {
  typedef const BBWrapper NodeType;
  typedef const_loop_pred_iterator ChildIteratorType;
  static NodeType *getEntryNode(Inverse<const BBWrapper*> G) { return G.Graph; }
  static inline ChildIteratorType child_begin(NodeType *N) {
    return loop_pred_begin(N);
  }
  static inline ChildIteratorType child_end(NodeType *N) {
    return loop_pred_end(N);
  }
};

// Provide specializations of GraphTraits to be able to treat a function as a
// graph of basic blocks... these are the same as the basic block iterators,
// except that the root node is implicitly the first node of the function.
//
template <> struct GraphTraits<const LoopWrapper*> :
  public GraphTraits<const BBWrapper*> {
  static NodeType *getEntryNode(const LoopWrapper *LW) { 
    return LW->get(LW->L->getHeader());
  }

  // nodes_iterator/begin/end - Allow iteration over all nodes in the graph
  typedef std::vector<const BBWrapper*>::const_iterator nodes_iterator;
  static nodes_iterator nodes_begin(const LoopWrapper *LW) { return LW->BBs.begin(); }
  static nodes_iterator nodes_end  (const LoopWrapper *LW) { return LW->BBs.end(); }
};


// Provide specializations of GraphTraits to be able to treat a function as a
// graph of basic blocks... and to walk it in inverse order.  Inverse order for
// a function is considered to be when traversing the predecessor edges of a BB
// instead of the successor edges.
//
template <> struct GraphTraits<Inverse<const LoopWrapper*> > :
  public GraphTraits<Inverse<const BBWrapper*> > {
  static NodeType *getEntryNode(Inverse<const LoopWrapper*> G) {
    return G.Graph->get(G.Graph->L->getHeader());
  }
};

} // End namespace llvm



