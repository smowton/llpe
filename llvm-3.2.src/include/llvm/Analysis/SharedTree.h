#define HEAPTREEORDER 16
#define HEAPTREEORDERLOG2 4

#define LFV3(x) do {} while(0)
//#define LFV3(x) x

template<class, class> class MergeBlockVisitor;

template<class ChildType, class ExtraState> struct SharedTreeNode {

  // These point to SharedTreeNodes or ChildTypes if this is the bottom layer.
  void* children[HEAPTREEORDER];
  int refCount;

SharedTreeNode() : refCount(1) {

  memset(children, 0, sizeof(void*) * HEAPTREEORDER);

}

  void dropReference(uint32_t height);
  ChildType* getReadableStoreFor(uint32_t idx, uint32_t height);
  ChildType* getOrCreateStoreFor(uint32_t idx, uint32_t height, bool* isNewStore);
  SharedTreeNode* getWritableNode(uint32_t height);
  void mergeHeaps(SmallVector<SharedTreeNode<ChildType, ExtraState>*, 4>& others, bool allOthersClobbered, uint32_t height, uint32_t idx, MergeBlockVisitor<ChildType, ExtraState>* visitor);
  void print(raw_ostream&, bool brief, uint32_t height, uint32_t idx);

};

template<class ChildType, class ExtraState> 
void SharedTreeNode<ChildType, ExtraState>::dropReference(uint32_t height) {

  if(!--refCount) {

    LFV3(errs() << "Freeing node " << this << "\n");

    // This node goes away! Drop our children.
    if(height == 0) {

      for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {
	if(children[i]) {
	  ChildType* child = ((ChildType*)children[i]);
	  child->dropReference();
	  delete child;
	}
      }

    }
    else {

      for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {
	if(children[i])
	  ((SharedTreeNode*)children[i])->dropReference(height - 1);
      }

    }

    delete this;

  }

}

template<class ChildType, class ExtraState> 
ChildType* SharedTreeNode<ChildType, ExtraState>::getReadableStoreFor(uint32_t idx, uint32_t height) {

  uint32_t nextChild = (idx >> (height * HEAPTREEORDERLOG2)) & (HEAPTREEORDER-1);

  if(!children[nextChild])
    return 0;

  if(height == 0) {

    // Our children are leaves.
    return (ChildType*)children[nextChild];

  }
  else {

    // Walk further down the tree.
    return ((SharedTreeNode*)children[nextChild])->getReadableStoreFor(idx, height - 1);

  }

}

template<class ChildType, class ExtraState> ChildType* 
SharedTreeNode<ChildType, ExtraState>::getOrCreateStoreFor(uint32_t idx, uint32_t height, bool* isNewStore) {

  // This node already known writable.

  uint32_t nextChild = (idx >> (height * HEAPTREEORDERLOG2)) & (HEAPTREEORDER-1);
  
  if(height == 0) {
    
    bool mustCreate = *isNewStore = (children[nextChild] == 0);
    if(mustCreate)
      children[nextChild] = new ChildType();
    return (ChildType*)children[nextChild];

  }
  else {

    SharedTreeNode* child;

    if(!children[nextChild])
      child = new SharedTreeNode();
    else
      child = ((SharedTreeNode*)children[nextChild])->getWritableNode(height - 1);

    children[nextChild] = child;
    return child->getOrCreateStoreFor(idx, height - 1, isNewStore);

  }

}

template<class ChildType, class ExtraState> SharedTreeNode<ChildType, ExtraState>* 
SharedTreeNode<ChildType, ExtraState>::getWritableNode(uint32_t height) {

  if(refCount == 1)
    return this;

  // COW break this node.
  SharedTreeNode* newNode = new SharedTreeNode();

  if(height == 0) {

    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

      if(children[i])
	newNode->children[i] = new ChildType(((ChildType*)children[i])->getReadableCopy());
      
    }

  }
  else {

    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

      if(children[i]) {
	((SharedTreeNode*)children[i])->refCount++;
	newNode->children[i] = children[i];
      }

    }

  }

  // Drop ref to this node.
  --refCount;

  return newNode;

}

static bool derefLT(void** a, void** b) {
  if(!a)
    return !!b;
  else if(!b)
    return false;
  else
    return *a < *b;
}

static bool derefEQ(void** a, void** b) {

  if(!a)
    return !b;
  else if(!b)
    return false;
  else
    return (*a == *b);

}

template<class Base> struct IndirectComp {

  static bool LT(void** a, void** b) {

    if(!a)
      return !!b;
    else if(!b)
      return false;
    else
      return Base::LT((Base*)*a, (Base*)*b);

  }

  static bool EQ(void** a, void** b) {

    if(!a)
      return !b;
    else if(!b)
      return false;
    else
      return Base::EQ((Base*)*a, (Base*)*b);

  }

};

ShadowValue& getAllocWithIdx(int32_t);

template<class ChildType, class ExtraState> 
void SharedTreeNode<ChildType, ExtraState>
  ::mergeHeaps(SmallVector<SharedTreeNode<ChildType, ExtraState>*, 4>& others, 
	       bool allOthersClobbered, uint32_t height, uint32_t idx, 
	       MergeBlockVisitor<ChildType, ExtraState>* visitor) {

  // All members of others are known to differ from this node. This node is writable already.
  // Like the frames case, merge in base objects when objects are missing from this or the other tree
  // if !allOthersClobbered; otherwise intersect the trees.
  // Note the special case that others might contain a null pointer, which describes the empty tree.

  if(allOthersClobbered) {

    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

      for(typename SmallVector<SharedTreeNode<ChildType, ExtraState>*, 4>::iterator it = others.begin(), itend = others.end();
	  it != itend && children[i]; ++it) {

	if((!*it) || !((*it)->children[i])) {

	  if(height == 0)
	    delete ((ChildType*)children[i]);
	  else
	    ((SharedTreeNode*)children[i])->dropReference(height - 1);
	  children[i] = 0;

	}

      }

    }

  }
  else {

    // Populate this node with base versions of nodes that are missing but present in any other tree. 
    // Just add blank nodes for now and then the recursion will catch the rest.
    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

      ShadowValue& MergeV = getAllocWithIdx(idx + i);

      for(typename SmallVector<SharedTreeNode<ChildType, ExtraState>*, 4>::iterator it = others.begin(), 
	    itend = others.end(); it != itend && !children[i]; ++it) {

	if((*it) && (*it)->children[i]) {

	  if(height == 0)
	    children[i] = new ChildType(ChildType::getEmptyStore().getReadableCopy());
	  else
	    children[i] = new SharedTreeNode();

	}

      }

    }

  }

  // OK now merge each child that exists according to the same rules.

  for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

    if(!children[i])
      continue;

    // Unique children regardless of whether they're further levels of TreeNode
    // or ChildTypes. In the former case this avoids merges of identical subtrees
    // in the latter it skips merging ChildTypes that are shared (as determined by ChildType::EQ)
    // In either case refcounting is caught up when unused maps are released at the top level.
    SmallVector<void**, 4> incomingPtrs;
    incomingPtrs.reserve(std::distance(others.begin(), others.end()) + 1);

    incomingPtrs.push_back(&(children[i]));

    for(typename SmallVector<SharedTreeNode<ChildType, ExtraState>*, 4>::iterator it = others.begin(), itend = others.end();
	it != itend; ++it) {

      if((!*it) || !(*it)->children[i])
	incomingPtrs.push_back(0);
      else
	incomingPtrs.push_back(&((*it)->children[i]));

    }

    if(height == 0) {

      std::sort(incomingPtrs.begin(), incomingPtrs.end(), IndirectComp<ChildType>::LT);
      SmallVector<void**, 4>::iterator uniqend = std::unique(incomingPtrs.begin(), incomingPtrs.end(), IndirectComp<ChildType>::EQ);
      
      // This subtree never differs?
      if(std::distance(incomingPtrs.begin(), uniqend) == 1)
	continue;

      // Merge each child value.
      for(SmallVector<void**, 4>::iterator it = incomingPtrs.begin(); it != uniqend; ++it) {
	
	if(*it == &(children[i]))
	  continue;

	ShadowValue& MergeV = getAllocWithIdx(idx + i);

	ChildType* mergeFromStore;
	if(!*it)
	  mergeFromStore = &ChildType::getEmptyStore();
	else
	  mergeFromStore = (ChildType*)(**it);

	// mergeStores takes care of CoW break if necessary.
	ChildType::mergeStores(mergeFromStore, (ChildType*)children[i], MergeV, visitor);
	((ChildType*)children[i])->checkMergedResult(MergeV);
      
      }

    }
    else {

      std::sort(incomingPtrs.begin(), incomingPtrs.end(), derefLT);
      SmallVector<void**, 4>::iterator uniqend = std::unique(incomingPtrs.begin(), incomingPtrs.end(), derefEQ);
      
      // This subtree never differs?
      if(std::distance(incomingPtrs.begin(), uniqend) == 1)
	continue;

      // Recursively merge this child.
      // CoW break this subtree if necessary.
      children[i] = ((SharedTreeNode*)children[i])->getWritableNode(height - 1);

      uint32_t newIdx = idx | (i << (HEAPTREEORDERLOG2 * height));
      SmallVector<SharedTreeNode*, 4> otherChildren;
      for(SmallVector<void**, 4>::iterator it = incomingPtrs.begin(), itend = incomingPtrs.end();
	  it != itend; ++it) {
	
	if(!*it)
	  otherChildren.push_back(0);
	else
	  otherChildren.push_back((SharedTreeNode*)**it);

      }

      ((SharedTreeNode*)children[i])->mergeHeaps(otherChildren, allOthersClobbered, height - 1, newIdx, visitor);

    }

  }

}

void printSV(raw_ostream&, ShadowValue);

template<class ChildType, class ExtraState> void SharedTreeNode<ChildType, ExtraState>::print(raw_ostream& RSO, bool brief, uint32_t height, uint32_t idx) {

  if(height == 0) {
    
    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {
      if(!children[i])
	continue;
      printSV(RSO, getAllocWithIdx(idx + i));
      RSO << ": ";
      ((ChildType*)children[i])->print(RSO, brief);
      RSO << "\n";
    }

  }
  else {
  
    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {
      if(!children[i])
	continue;
      uint32_t newIdx = idx | (i << (HEAPTREEORDERLOG2 * height));
      ((SharedTreeNode*)children[i])->print(RSO, brief, height - 1, newIdx);
    }
     
  } 

}

template<class ChildType, class ExtraState> struct SharedTreeRoot {

  SharedTreeNode<ChildType, ExtraState>* root;
  uint32_t height;

SharedTreeRoot() : root(0), height(0) { }
  void clear();
  void dropReference();
  ChildType* getReadableStoreFor(ShadowValue& V);
  ChildType* getOrCreateStoreFor(ShadowValue& V, bool* isNewStore);
  void growToHeight(uint32_t newHeight);
  void grow(uint32_t idx);
  bool mustGrowFor(uint32_t idx);

};

static uint32_t getRequiredHeight(uint32_t idx) {

  uint32_t height = 0;

  do {

    idx >>= HEAPTREEORDERLOG2;
    ++height;

  } while(idx);

  return height;

}

template<class ChildType, class ExtraState> ChildType* SharedTreeRoot<ChildType, ExtraState>::getReadableStoreFor(ShadowValue& V) {

  // Empty heap?
  if(height == 0)
    return 0;

  // Is a valid allocation instruction?
  int32_t idx = V.getHeapKey();
  if(idx < 0)
   return 0;

  if(getRequiredHeight(idx) > height)
    return 0;

  // OK search:
  return root->getReadableStoreFor((uint32_t)idx, height - 1);

}

template<class ChildType, class ExtraState> void SharedTreeRoot<ChildType, ExtraState>::growToHeight(uint32_t newHeight) {

  for(uint32_t i = 0, ilim = (newHeight - height); i != ilim; ++i) {

    SharedTreeNode<ChildType, ExtraState>* newNode = new SharedTreeNode<ChildType, ExtraState>();
    newNode->children[0] = root;
    root = newNode;

  }

  height = newHeight;

}

template<class ChildType, class ExtraState> void SharedTreeRoot<ChildType, ExtraState>::grow(uint32_t idx) {

  // Need to make the tree taller first (hopefully the above test is cheaper than getReqdHeight)
  uint32_t newHeight = getRequiredHeight(idx);
  growToHeight(newHeight);

}

template<class ChildType, class ExtraState> bool SharedTreeRoot<ChildType, ExtraState>::mustGrowFor(uint32_t idx) {

  // Can't accommodate more than 2^32 heap items! Change this if we use a uint64_t for heap indices.
  if(height == (32 / HEAPTREEORDERLOG2))
    return false;

  return idx >= (uint32_t)(HEAPTREEORDER << ((height - 1) * HEAPTREEORDERLOG2));

}

template<class ChildType, class ExtraState> ChildType* SharedTreeRoot<ChildType, ExtraState>::getOrCreateStoreFor(ShadowValue& V, bool* isNewStore) {

  int32_t idx = V.getHeapKey();

  if(idx < 0)
    release_assert(0 && "Tried to write to non-allocation?");

  if(!root) {

    // Empty heap.
    root = new SharedTreeNode<ChildType, ExtraState>();
    height = getRequiredHeight(idx);

  }
  else if(mustGrowFor(idx)) {

    grow(idx);

  }
  else {

    root = root->getWritableNode(height - 1);

  }

  return root->getOrCreateStoreFor(idx, height - 1, isNewStore);

}

template<class ChildType, class ExtraState> void SharedTreeRoot<ChildType, ExtraState>::clear() {

  if(height == 0)
    return;
  root->dropReference(height - 1);
  root = 0;
  height = 0;

}

template<class ChildType, class ExtraState> void SharedTreeRoot<ChildType, ExtraState>::dropReference() {

  clear();

}

template<class ChildType, class ExtraState> struct SharedStoreMap {

  std::vector<ChildType> store;
  uint32_t refCount;
  InlineAttempt* IA;
  bool empty;

SharedStoreMap(InlineAttempt* _IA, uint32_t initSize) : store(initSize), refCount(1), IA(_IA), empty(true) { }

  SharedStoreMap* getWritableStoreMap();
  void dropReference();
  void clear();
  SharedStoreMap* getEmptyMap();
  void print(raw_ostream&, bool brief);

};

template<class ChildType, class ExtraState> SharedStoreMap<ChildType, ExtraState>* SharedStoreMap<ChildType, ExtraState>::getWritableStoreMap() {

  // Refcount == 1 means we can just write in place.
  if(refCount == 1) {
    LFV3(errs() << "Local map " << this << " already writable\n");
    return this;
  }

  // COW break: copy the map and either share or copy its entries.
  LFV3(errs() << "COW break local map " << this << " with " << store.size() << " entries\n");
  SharedStoreMap* newMap = new SharedStoreMap(IA, store.size());

  uint32_t i = 0;
  for(typename std::vector<ChildType>::iterator it = store.begin(), it2 = store.end(); it != it2; ++it, ++i) {
    if(!it->isValid())
      continue;
    newMap->store[i] = it->getReadableCopy();
    newMap->empty = false;
  }

  // Drop reference on the existing map (can't destroy it):
  refCount--;
  
  return newMap;

}

int32_t getFrameSize(InlineAttempt*);
bool hasNoCallers(InlineAttempt*);

static int32_t allocFrameSize(InlineAttempt* IA) {

  uint32_t frameSize = getFrameSize(IA);
  if(frameSize == (uint32_t)-1) {

    release_assert(hasNoCallers(IA)
		   && "Call with no allocas should only be given a frame if it is the root.");
    return 0;

  }  
  else {

    return frameSize;

  }

}

template<class ChildType, class ExtraState> void SharedStoreMap<ChildType, ExtraState>::clear() {

  release_assert(refCount <= 1 && "clear() against shared map?");

  // Drop references to any maps this points to;
  for(typename std::vector<ChildType>::iterator it = store.begin(), itend = store.end(); it != itend; ++it) {
    if(!it->isValid())
      continue;
    it->dropReference();
  }

  store.clear();
  store.resize(allocFrameSize(IA));
  empty = true;

}

template<class ChildType, class ExtraState> SharedStoreMap<ChildType, ExtraState>* SharedStoreMap<ChildType, ExtraState>::getEmptyMap() {

  if(!store.size())
    return this;
  else if(refCount == 1) {
    clear();
    return this;
  }
  else {
    dropReference();
    return new SharedStoreMap<ChildType, ExtraState>(IA, store.size());
  }

}

template<class ChildType, class ExtraState> void SharedStoreMap<ChildType, ExtraState>::dropReference() {

  if(!--refCount) {

    LFV3(errs() << "Local map " << this << " freed\n");
    clear();

    delete this;

  }
  else {

    LFV3(errs() << "Local map " << this << " refcount down to " << refCount << "\n");

  }

}

ShadowValue getStackAllocationWithIndex(InlineAttempt*, uint32_t);

template<class ChildType, class ExtraState> void SharedStoreMap<ChildType, ExtraState>::print(raw_ostream& RSO, bool brief) {

  uint32_t i = 0;
  for(typename std::vector<ChildType>::iterator it = store.begin(), itend = store.end(); it != itend; ++it, ++i) {

    printSV(RSO, getStackAllocationWithIndex(IA, i));
    RSO << ": ";
    it->print(RSO, brief);
    RSO << "\n";

  }

}

template<class ChildType, class ExtraState> struct LocalStoreMap {

  typedef SharedStoreMap<ChildType, ExtraState> FrameType;
  typedef SharedTreeRoot<ChildType, ExtraState> RootType;
  typedef SharedTreeNode<ChildType, ExtraState> NodeType;

  SmallVector<FrameType*, 4> frames;
  RootType heap;

  bool allOthersClobbered;
  uint32_t refCount;

  ExtraState es;

LocalStoreMap(uint32_t s) : frames(s), heap(), allOthersClobbered(false), refCount(1) {}

  void clear();
  LocalStoreMap* getEmptyMap();
  void dropReference();
  LocalStoreMap* getWritableFrameList();
  void print(raw_ostream&, bool brief = false);
  bool empty();
  void copyEmptyFrames(SmallVector<SharedStoreMap<ChildType, ExtraState>*, 4>&);
  void copyFramesFrom(const LocalStoreMap<ChildType, ExtraState>&);
  std::vector<ChildType>& getWritableFrame(int32_t frameNo);
  void pushStackFrame(InlineAttempt*);
  void popStackFrame();
  ChildType* getReadableStoreFor(ShadowValue& V);
  ChildType* getOrCreateStoreFor(ShadowValue& V, bool* isNewStore);

};

template<class ChildType, class ExtraState>
ChildType* LocalStoreMap<ChildType, ExtraState>::getOrCreateStoreFor(ShadowValue& V, bool* isNewStore) {

  int32_t frameNo = V.getFrameNo();
  if(frameNo != -1) {

    std::vector<ChildType>& frameMap = getWritableFrame(frameNo);
    frames[frameNo]->empty = false;
    int32_t framePos = V.u.I->getAllocData()->allocIdx;
    release_assert(framePos >= 0 && "Stack entry without an index?");
    if(frameMap.size() <= (uint32_t)framePos)
      frameMap.resize(framePos + 1);
    *isNewStore = !(frameMap[framePos].isValid());
    return &(frameMap[framePos]);

  }
  else {

    return heap.getOrCreateStoreFor(V, isNewStore);

  }

}

template<class ChildType, class ExtraState> ChildType* LocalStoreMap<ChildType, ExtraState>::getReadableStoreFor(ShadowValue& V) {
  
  int32_t frameNo = V.getFrameNo();
  if(frameNo == -1)
    return heap.getReadableStoreFor(V);
  else {

    std::vector<ChildType>& frame = frames[frameNo]->store;
    uint32_t frameIdx = V.u.I->getAllocData()->allocIdx;
    if(frame.size() <= frameIdx)
      return 0;

    ChildType* ret = &(frame[frameIdx]);
    if(!ret->isValid())
      return 0;
    else
      return ret;

  }
  
}

template<class ChildType, class ExtraState> LocalStoreMap<ChildType, ExtraState>* LocalStoreMap<ChildType, ExtraState>::getWritableFrameList() {

  if(refCount == 1)
    return this;

  LocalStoreMap<ChildType, ExtraState>* newMap = new LocalStoreMap<ChildType, ExtraState>(frames.size());
  newMap->copyFramesFrom(*this);

  newMap->allOthersClobbered = allOthersClobbered;

  // Can't destory, as refCount > 1
  --refCount;

  return newMap;

}

template<class ChildType, class ExtraState> std::vector<ChildType>& LocalStoreMap<ChildType, ExtraState>::getWritableFrame(int32_t frameNo) {

  release_assert(frameNo >= 0 && frameNo < (int32_t)frames.size());
  frames[frameNo] = frames[frameNo]->getWritableStoreMap();
  return frames[frameNo]->store;

}

template<class ChildType, class ExtraState> void LocalStoreMap<ChildType, ExtraState>::clear() {

  heap.clear();
  for(uint32_t i = 0; i < frames.size(); ++i)
    frames[i] = frames[i]->getEmptyMap();

}

template<class ChildType, class ExtraState> bool LocalStoreMap<ChildType, ExtraState>::empty() {

  if(heap.height != 0)
    return false;

  for(uint32_t i = 0; i < frames.size(); ++i) {
    if(!frames[i]->empty)
      return false;
  }

  return true;

}

template<class ChildType, class ExtraState> LocalStoreMap<ChildType, ExtraState>* LocalStoreMap<ChildType, ExtraState>::getEmptyMap() {

  if(empty())
    return this;
  else if(refCount == 1) {
    clear();
    return this;
  }
  else {
    // Can't free the map (refcount > 1)
    --refCount;
    LocalStoreMap<ChildType, ExtraState>* newMap = new LocalStoreMap<ChildType, ExtraState>(frames.size());
    newMap->copyEmptyFrames(frames);
    return newMap;
  }

}

template<class ChildType, class ExtraState> void LocalStoreMap<ChildType, ExtraState>::copyEmptyFrames(SmallVector<SharedStoreMap<ChildType, ExtraState>*, 4>& copyFrom) {

  // Heap starts in empty state.
  // Copy metadata per frame but don't populate any objects.
  for(uint32_t i = 0; i < frames.size(); ++i) {
    
    uint32_t newFrameSize = allocFrameSize(copyFrom[i]->IA);
    frames[i] = new SharedStoreMap<ChildType, ExtraState>(copyFrom[i]->IA, newFrameSize);
  }

}

template<class ChildType, class ExtraState> void LocalStoreMap<ChildType, ExtraState>::copyFramesFrom(const LocalStoreMap<ChildType, ExtraState>& other) {

  // Frames array already allocated. Borrow all the other side's frames.

  heap = other.heap;
  if(heap.root)
    heap.root->refCount++;

  for(uint32_t i = 0; i < frames.size(); ++i) {

    frames[i] = other.frames[i];
    frames[i]->refCount++;

  }

  es.copyFrom(other.es);
  
}

template<class ChildType, class ExtraState> void LocalStoreMap<ChildType, ExtraState>::dropReference() {

  if(!--refCount) {

    LFV3(errs() << "Local map " << this << " freed\n");
    heap.dropReference();
    for(uint32_t i = 0; i < frames.size(); ++i)
      frames[i]->dropReference();

    delete this;

  }
  else {

    LFV3(errs() << "Local map " << this << " refcount down to " << refCount << "\n");

  }

}

template<class ChildType, class ExtraState> void LocalStoreMap<ChildType, ExtraState>::popStackFrame() {

  release_assert(frames.size() && "Pop from empty stack?");
  frames.back()->dropReference();
  frames.pop_back();

}

template<class ChildType, class ExtraState> void LocalStoreMap<ChildType, ExtraState>::pushStackFrame(InlineAttempt* IA) {

  frames.push_back(new SharedStoreMap<ChildType, ExtraState>(IA, allocFrameSize(IA)));

}

template<class ChildType, class ExtraState> void LocalStoreMap<ChildType, ExtraState>::print(raw_ostream& RSO, bool brief) {

  errs() << "--- Stack ---\n";
  for(uint32_t i = 0; i < frames.size(); ++i) {
    if(i != 0)
      errs() << "---frame boundary---\n";
    frames[i]->print(RSO, brief);
  }
  errs() << "--- End stack ---\n--- Heap ---\n";
  if(!heap.root)
    errs() << "(empty)\n";
  else
    heap.root->print(RSO, brief, heap.height - 1, 0);
  errs() << "--- End heap ---\n";

}

template<class ChildType, class ExtraState> struct MergeBlockVisitor : public ShadowBBVisitor {

  typedef LocalStoreMap<ChildType, ExtraState> MapType;
  typedef SharedStoreMap<ChildType, ExtraState> FrameType;
  typedef SharedTreeRoot<ChildType, ExtraState> RootType;
  typedef SharedTreeNode<ChildType, ExtraState> NodeType;
   
  MapType* newMap;
  bool mergeToBase;
  bool useVarargMerge;
  SmallVector<ShadowBB*, 4> incomingBlocks;
  bool verbose;
   
 MergeBlockVisitor(bool mtb, bool uvm = false, bool v = false) : ShadowBBVisitor(true), newMap(0), mergeToBase(mtb), useVarargMerge(uvm), verbose(v) { }
   
  void mergeFrames(MapType* toMap, typename SmallVector<MapType*, 4>::iterator fromBegin, typename SmallVector<MapType*, 4>::iterator fromEnd, uint32_t idx);
  void mergeHeaps(MapType* toMap, typename SmallVector<MapType*, 4>::iterator fromBegin, typename SmallVector<MapType*, 4>::iterator fromEnd);
  void mergeFlags(MapType* toMap, typename SmallVector<MapType*, 4>::iterator fromBegin, typename SmallVector<MapType*, 4>::iterator fromEnd);
  void visit(ShadowBB* BB, void* Ctx, bool mustCopyCtx) {
    incomingBlocks.push_back(BB);
  }
  void doMerge();

};

// Comparator for finding the best target heap: we want the tallest heap, and of those, we favour a writable one. Finally compare pointers.
template<class ChildType, class ExtraState> bool rootTallerThan(const LocalStoreMap<ChildType, ExtraState>* r1, const LocalStoreMap<ChildType, ExtraState>* r2) {

  if(r1->heap.height != r2->heap.height)
    return r1->heap.height > r2->heap.height;

  return r1->heap.root > r2->heap.root;
  
}

template<class ChildType, class ExtraState> bool rootsEqual(const LocalStoreMap<ChildType, ExtraState>* r1, const LocalStoreMap<ChildType, ExtraState>* r2) {

  return r1->heap.root == r2->heap.root && r1->heap.height == r2->heap.height;

}

template<class ChildType, class ExtraState> 
void MergeBlockVisitor<ChildType, ExtraState>::
  mergeHeaps(MapType* toMap, 
	     typename SmallVector<MapType*, 4>::iterator fromBegin, 
	     typename SmallVector<MapType*, 4>::iterator fromEnd) {

  SmallVector<MapType*, 4> incomingRoots;
  incomingRoots.reserve(std::distance(fromBegin, fromEnd) + 1);

  incomingRoots.push_back(toMap);
  for(typename SmallVector<MapType*, 4>::iterator it = fromBegin; it != fromEnd; ++it)
    incomingRoots.push_back(*it);

  /*
  errs() << "Target heap:\n";
  if(toMap->heap.root)
    toMap->heap.root->print(errs(), false, toMap->heap.height - 1, 0);

  for(SmallVector<LocalStoreMap*, 4>::iterator it = fromBegin; it != fromEnd; ++it) {
    errs() << "Merging in:\n";
    if((*it)->heap.root)
      (*it)->heap.root->print(errs(), false, (*it)->heap.height - 1, 0);
  }
  */

  // This sorts first by heap height, then by pointer address, so it also finds the tallest heap.
  std::sort(incomingRoots.begin(), incomingRoots.end(), rootTallerThan<ChildType, ExtraState>);
  typename SmallVector<MapType*, 4>::iterator uniqend = std::unique(incomingRoots.begin(), incomingRoots.end(), rootsEqual<ChildType, ExtraState>);
  
  // Heaps never differ?
  if(std::distance(incomingRoots.begin(), uniqend) == 1)
    return;

  release_assert(incomingRoots[0]->heap.height != 0 && "If heaps differ at least one must be initialised!");

  if(!toMap->heap.root) {

    // Target has no heap at all yet -- make one.
    toMap->heap.root = new NodeType();
    toMap->heap.height = 1;

  }
  else {

    // If necessary, CoW break the target heap.
    toMap->heap.root = toMap->heap.root->getWritableNode(toMap->heap.height - 1);

  }

  // Grow the target heap to the tallest height seen.
  if(toMap->heap.height != incomingRoots[0]->heap.height)
    toMap->heap.growToHeight(incomingRoots[0]->heap.height);

  // Start the tree merge:
  SmallVector<NodeType*, 4> roots;
  for(typename SmallVector<MapType*, 4>::iterator it = incomingRoots.begin(); it != uniqend; ++it) {

    if(toMap->heap.root == (*it)->heap.root)
      continue;

    LocalStoreMap<ChildType, ExtraState>* thisMap = *it;

    // Temporarily grow heaps that are shorter than the target to make the merge easier to code.
    // Leave their height attribute unchanged as an indicator we need to undo this shortly.
    // These maps might be shared so it's important they are seen unmodified ouside this function.
    if(thisMap->heap.height != 0 && thisMap->heap.height < toMap->heap.height) {
      uint32_t oldHeight = thisMap->heap.height;
      thisMap->heap.growToHeight(toMap->heap.height);
      thisMap->heap.height = oldHeight;
    }

    roots.push_back(thisMap->heap.root);

  }

  toMap->heap.root->mergeHeaps(roots, toMap->allOthersClobbered, toMap->heap.height - 1, 0, this);

  for(typename SmallVector<MapType*, 4>::iterator it = incomingRoots.begin(); it != uniqend; ++it) {

    if((*it)->heap.height == 0)
      continue;

    LocalStoreMap<ChildType, ExtraState>* thisMap = *it;
    uint32_t tempFramesToRemove = incomingRoots[0]->heap.height - thisMap->heap.height;

    for(uint32_t i = 0; i < tempFramesToRemove; ++i) {
      NodeType* removeNode = thisMap->heap.root;
      thisMap->heap.root = (NodeType*)thisMap->heap.root->children[0];
      release_assert(removeNode->refCount == 1 && "Removing shared node in post-treemerge cleanup?");
      delete removeNode;
    }

  }  

}

template<class ChildType, class ExtraState>
void MergeBlockVisitor<ChildType, ExtraState>::mergeFrames(MapType* toMap, typename SmallVector<MapType*, 4>::iterator fromBegin, typename SmallVector<MapType*, 4>::iterator fromEnd, uint32_t idx) {

  SmallVector<FrameType*, 4> incomingFrames;
  incomingFrames.reserve(std::distance(fromBegin, fromEnd) + 1);

  incomingFrames.push_back(toMap->frames[idx]);
  for(typename SmallVector<MapType*, 4>::iterator it = fromBegin; it != fromEnd; ++it)
    incomingFrames.push_back((*it)->frames[idx]);

  std::sort(incomingFrames.begin(), incomingFrames.end());
  typename SmallVector<FrameType*, 4>::iterator uniqend = std::unique(incomingFrames.begin(), incomingFrames.end());

  // Frames never differ?
  if(std::distance(incomingFrames.begin(), uniqend) == 1)
    return;

  // CoW break stack frame if necessary
  FrameType* mergeToFrame = toMap->frames[idx] = toMap->frames[idx]->getWritableStoreMap();
  std::vector<ChildType>& mergeToStore = mergeToFrame->store;

  InlineAttempt* thisFrameIA = mergeToFrame->IA;

  // Merge in each other frame. Note toMap->allOthersClobbered has been set to big-or over all maps already.
  for(typename SmallVector<FrameType*, 4>::iterator it = incomingFrames.begin(); it != uniqend; ++it) {

    FrameType* mergeFromFrame = *it;
    if(mergeFromFrame == mergeToFrame)
      continue;
    std::vector<ChildType>& mergeFromStore = mergeFromFrame->store;

    if(toMap->allOthersClobbered) {
      
      // Incremental big intersection of the incoming frames
      // Remove any in mergeTo that do not occur in mergeFrom.

      // Remove any existing mappings in mergeToFrame that do not occur in mergeFromFrame:

      for(uint32_t i = 0, ilim = mergeToStore.size(); i != ilim; ++i) {

	if(mergeToStore[i].isValid() && (i >= mergeFromStore.size() || !mergeFromStore[i].isValid())) {
	  mergeToStore[i].dropReference();
	  mergeToStore[i] = ChildType();
	}

      }

      if(mergeToStore.size() > mergeFromStore.size())
	mergeToStore.resize(mergeFromStore.size());

    }
    else {

      LFV3(errs() << "Both maps don't have allOthersClobbered; reading through allowed\n");

      // For any locations mentioned in mergeFromFrame but not mergeToFrame,
      // add a the relevant allocation's default object to mergeToFrame. 
      // This will get overwritten below but creates the asymmetry that 
      // x in mergeFromFrame -> x in mergeToFrame.

      if(mergeFromStore.size() > mergeToStore.size())
	mergeToStore.resize(mergeFromStore.size());

      for(uint32_t i = 0, ilim = mergeFromStore.size(); i != ilim; ++i) {
	  
	if(mergeFromStore[i].isValid() && !mergeToStore[i].isValid()) {
	  mergeToStore[i] = ChildType::getEmptyStore().getReadableCopy();
	  mergeToFrame->empty = false;
	}
	
      }
      
    }

  }

  // mergeToFrame now contains all objects that should be merged.
  // Note that in the allOthersClobbered case this only merges in
  // information from locations explicitly mentioned in all incoming frames.

  for(uint32_t i = 0, ilim = mergeToStore.size(); i != ilim; ++i) {

    if(!mergeToStore[i].isValid())
      continue;

    ChildType* mergeToLoc = &(mergeToStore[i]);

    ShadowValue mergeSV = ShadowValue(getStackAllocationWithIndex(thisFrameIA, i));

    SmallVector<ChildType*, 4> incomingStores;

    for(typename SmallVector<SharedStoreMap<ChildType, ExtraState>*, 4>::iterator incit = incomingFrames.begin(); incit != uniqend; ++incit) {

      SharedStoreMap<ChildType, ExtraState>* mergeFromFrame = *incit;
      if(mergeFromFrame == mergeToFrame)
	continue;

      ChildType* mergeFromLoc;

      if(mergeFromFrame->store.size() > i && mergeFromFrame->store[i].isValid())
	mergeFromLoc = &(mergeFromFrame->store[i]);
      else
	mergeFromLoc = &(ChildType::getEmptyStore());

      incomingStores.push_back(mergeFromLoc);

    }

    std::sort(incomingStores.begin(), incomingStores.end(), ChildType::LT);
    typename SmallVector<ChildType*, 4>::iterator storeuniqend = 
      std::unique(incomingStores.begin(), incomingStores.end(), ChildType::EQ);

    for(typename SmallVector<ChildType*, 4>::iterator incit = incomingStores.begin(), incitend = incomingStores.end();
	incit != incitend; ++incit) {

      ChildType* mergeFromLoc = *incit;

      // Right, merge it->second and mergeFromLoc.
      ChildType::mergeStores(mergeFromLoc, mergeToLoc, mergeSV, this);
      mergeToLoc->checkMergedResult(mergeSV);

    }

    ChildType::simplifyStore(mergeToLoc);

  }

}

template<class ChildType, class ExtraState>
void MergeBlockVisitor<ChildType, ExtraState>::doMerge() {

  if(incomingBlocks.empty())
    return;

  // Discard wholesale block duplicates:
  SmallVector<MapType*, 4> incomingStores;
  incomingStores.reserve(std::distance(incomingBlocks.begin(), incomingBlocks.end()));

  for(SmallVector<ShadowBB*, 4>::iterator it = incomingBlocks.begin(), itend = incomingBlocks.end();
      it != itend; ++it) {

    incomingStores.push_back(ChildType::getMapForBlock(*it));

  }

  std::sort(incomingStores.begin(), incomingStores.end());
  typename SmallVector<MapType*, 4>::iterator uniqend = std::unique(incomingStores.begin(), incomingStores.end());

  MapType* retainMap;
  
  if(std::distance(incomingStores.begin(), uniqend) > 1) {

    // At least some stores differ; need to make a new one.

    // See if we can avoid a CoW break by using a writable incoming store as the target.
    for(typename SmallVector<MapType*, 4>::iterator it = incomingStores.begin(); it != uniqend; ++it) {
      
      if((*it)->refCount == 1) {

	if(it != incomingStores.begin())
	  std::swap(incomingStores[0], *it);
	break;

      }

    }

    // Position 0 is the target; the rest should be merged in. CoW break if still necessary:
    // Note retainMap is set to the original map rather than the new one as the CoW break drops
    // a reference to it so it should not be unref'd again below.
    retainMap = incomingStores[0];
    MapType* mergeMap = incomingStores[0] = incomingStores[0]->getWritableFrameList();
    LFV3(errs() << "Merge target will be " << mergeMap << "\n");

    typename SmallVector<MapType*, 4>::iterator firstMergeFrom = incomingStores.begin();
    ++firstMergeFrom;

    for(typename SmallVector<MapType*, 4>::iterator it = firstMergeFrom; 
	it != uniqend && !mergeMap->allOthersClobbered; ++it) {

      if((*it)->allOthersClobbered)
	mergeMap->allOthersClobbered = true;

    }
   
    // Merge each frame, passing the InlineAttempt corresponding to each frame in turn.
    for(uint32_t i = 0; i < mergeMap->frames.size(); ++i)
      mergeFrames(mergeMap, firstMergeFrom, uniqend, i);

    mergeHeaps(mergeMap, firstMergeFrom, uniqend);

    ExtraState::doMerge(mergeMap, firstMergeFrom, uniqend, verbose);

    newMap = mergeMap;

  }
  else {

    // No stores differ; just use #0
    newMap = incomingStores[0];
    retainMap = newMap;

    if(verbose)
      ExtraState::dump(newMap);

  }

  // Drop refs against each incoming store apart from the store that was either used or
  // implicitly unref'd as part of the CoW break at getWritableFrameMap.

  for(SmallVector<ShadowBB*, 4>::iterator it = incomingBlocks.begin(), itend = incomingBlocks.end();
      it != itend; ++it) {

    MapType* thisMap = ChildType::getMapForBlock(*it);
    if(thisMap == retainMap)
      retainMap = 0;
    else
      thisMap->dropReference();

  }

}
