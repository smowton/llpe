
#include <vector>
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/DOTGraphTraits.h"
#include "llvm/Instruction.h"

#ifndef LLVM_SUPPORT_VFSGRAPH_H
#define LLVM_SUPPORT_VFSGRAPH_H

namespace llvm {

  class VFSGraphNode {

  public:
    std::vector<VFSGraphNode*> preds;
    std::vector<VFSGraphNode*> succs;
    Instruction* I;
    
  };

  class VFSGraph {

  public:
    Instruction* RootInstruction;
    llvm::DenseMap<Instruction*, VFSGraphNode> instructionNodes;

    VFSGraph(Instruction* RI) : RootInstruction(RI) { 

      nameNode(RI);

    }

    void addLink(Instruction* source, Instruction* dest) {

      VFSGraphNode* sourceNode = &instructionNodes[source];
      VFSGraphNode* destNode = &instructionNodes[dest];
      sourceNode->succs.push_back(destNode);
      destNode->preds.push_back(sourceNode);

    }

    void nameNode(Instruction* I) {

      instructionNodes[I].I = I;

    }
    
  };

  template <typename KeyT, typename ValueT> class DenseMapValueIterator {

  public:

    typename llvm::DenseMap<KeyT, ValueT>::iterator myIterator;
    typedef std::forward_iterator_tag iterator_category;

    DenseMapValueIterator(llvm::DenseMap<KeyT, ValueT>& map, bool end) { 
      if(end)
	myIterator = map.end();
      else
	myIterator = map.begin();
    }

    DenseMapValueIterator() { }

    ValueT& operator*() {

      return myIterator->second;

    }

    ValueT* operator->() {

      return &(myIterator->second);

    }

    bool operator==(const DenseMapValueIterator<KeyT, ValueT>& other) {

      return this->myIterator == other.myIterator;

    }

    bool operator!=(const DenseMapValueIterator<KeyT, ValueT>& other) {

      return this->myIterator != other.myIterator;

    }

    DenseMapValueIterator<KeyT, ValueT>& operator++() {

      myIterator++;
      return *this;

    }

    DenseMapValueIterator<KeyT, ValueT> operator++(int x) {

      DenseMapValueIterator<KeyT, ValueT> old = *this;
      myIterator++;
      return old;

    }
    

  };

  template <> struct GraphTraits<VFSGraph*> {

    typedef VFSGraphNode NodeType;
    typedef std::vector<VFSGraphNode*>::iterator ChildIteratorType;
    
    static ChildIteratorType child_begin(NodeType* N) { return N->succs.begin(); }
    static ChildIteratorType child_end(NodeType* N) { return N->succs.end(); }

    static NodeType *getEntryNode(VFSGraph* G) { return &G->instructionNodes[G->RootInstruction]; }

    // nodes_iterator/begin/end - Allow iteration over all nodes in the graph
    typedef DenseMapValueIterator<Instruction*, VFSGraphNode> nodes_iterator;
    static nodes_iterator nodes_begin(VFSGraph *G) { return nodes_iterator(G->instructionNodes, false); }
    static nodes_iterator nodes_end  (VFSGraph *G) { return nodes_iterator(G->instructionNodes, true); }

  };

  template <> struct DOTGraphTraits<VFSGraph*> : DefaultDOTGraphTraits {

  DOTGraphTraits(bool b = false) : DefaultDOTGraphTraits(b) { }

    std::string getNodeLabel(const VFSGraphNode* Node, VFSGraph* const Graph) {
      
      std::string output;
      llvm::raw_string_ostream os(output);
      os << *(Node->I);
      return os.str();

    }

  };

}

#endif
