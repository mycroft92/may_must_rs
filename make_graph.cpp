#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <vector>

using namespace llvm;

class ProgramGraph {
private:
    struct Node {
        const Instruction* inst;
        std::vector<Node*> successors;
        Node(const Instruction* i) : inst(i) {}
    };
    
    std::map<const Instruction*, Node*> nodes;

public:
    void addInstruction(const Instruction* inst) {
        if (nodes.find(inst) == nodes.end()) {
            nodes[inst] = new Node(inst);
        }
    }

    void addEdge(const Instruction* from, const Instruction* to) {
        Node* fromNode = nodes[from];
        Node* toNode = nodes[to];
        fromNode->successors.push_back(toNode);
    }

    void printGraph(raw_ostream& OS) {
        OS << "digraph ProgramGraph {\n";
        for (const auto& pair : nodes) {
            const Instruction* inst = pair.first;
            Node* node = pair.second;
            
            OS << "  Node" << inst << " [label=\"";
            inst->print(OS);
            OS << "\"];\n";

            for (Node* succ : node->successors) {
                OS << "  Node" << inst << " -> Node" << succ->inst << ";\n";
            }
        }
        OS << "}\n";
    }

    ~ProgramGraph() {
        for (auto& pair : nodes) {
            delete pair.second;
        }
    }
};

int main(int argc, char **argv) {
    if (argc < 2) {
        errs() << "Usage: " << argv[0] << " <IR file>\n";
        return 1;
    }

    // Parse the input LLVM IR file
    LLVMContext Context;
    SMDiagnostic Err;
    std::unique_ptr<Module> M = parseIRFile(argv[1], Err, Context);
    
    if (!M) {
        Err.print(argv[0], errs());
        return 1;
    }

    ProgramGraph graph;

    // Iterate through all functions
    for (Function &F : *M) {
        // Skip declarations
        if (F.isDeclaration())
            continue;

        // Iterate through all basic blocks
        for (BasicBlock &BB : F) {
            Instruction* prevInst = nullptr;

            // Iterate through all instructions
            for (Instruction &I : BB) {
                graph.addInstruction(&I);
                
                // Connect to previous instruction in the same basic block
                if (prevInst) {
                    graph.addEdge(prevInst, &I);
                }

                // Handle branch instructions
                if (BranchInst* br = dyn_cast<BranchInst>(&I)) {
                    for (unsigned i = 0; i < br->getNumSuccessors(); ++i) {
                        BasicBlock* succBB = br->getSuccessor(i);
                        if (!succBB->empty()) {
                            graph.addInstruction(&succBB->front());
                            graph.addEdge(&I, &succBB->front());
                        }
                    }
                }

                prevInst = &I;
            }
        }
    }

    // Output the graph in DOT format
    graph.printGraph(outs());

    return 0;
}
