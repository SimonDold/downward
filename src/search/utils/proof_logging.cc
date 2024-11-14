#include "proof_logging.h"

#include <fstream>
#include <iostream>
#include <sstream>

using namespace std;

namespace utils {

ProofLog::ProofLog(const string &reifications_file_name,
    const string &derivations_file_name)
    :
    reifications_file_name(reifications_file_name),
    derivations_file_name(derivations_file_name)
    {
        std::ofstream reifications_file(reifications_file_name);
        if (!reifications_file.is_open()) {
            std::cerr << "Failed to open file: "
                << reifications_file_name << std::endl;
        }
        reifications_file.close();

        std::ofstream derivations_file(derivations_file_name);
        if (!derivations_file.is_open()) {
            std::cerr << "Failed to open file: " 
                << derivations_file_name << std::endl;
        }
        derivations_file.close();
    }

void ProofLog::append_to_proof_log(const string &line, ProofPart proof_part)
{
    string file_name;
    switch (proof_part)
    {
    case ProofPart::REIFICATION:
        file_name = reifications_file_name;
        break;
    case ProofPart::DERIVATION:
        file_name = derivations_file_name;
        break;
    default:
        cerr << "Error: Not clear where to add." << std::endl;
        break;
    }

    ofstream file(file_name, std::ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening file for appending." << std::endl;
        return;
    }
    file << line << std::endl;
    file.close();
}

    void ProofLog::add_node_reification(optional<SearchNode> node){
        assert(node);
        State s = node->get_state();
        s.unpack();
        ostringstream line;
        line << "R-reification r" << s.get_id() << ": ~r" << s.get_id();
        vector<int> values = s.get_unpacked_values();
        for (unsigned int i = 0; i < values.size(); ++i) {
            line << " + v" << i << "_"<< values[i];
        }
        line << " + cost_geq_" << node->get_real_g() 
            << " >= " << values.size()+1 << ";";
        append_to_proof_log(line.str(), ProofPart::REIFICATION);
    }


    void ProofLog::add_node_action_invariant(OperatorID op_id, optional<SearchNode> node){
        assert(node);
        ostringstream line;
        line << "rup: ~node" << node->get_state().get_id() << "_g" << node->get_g() << " + ~action" << op_id << " + invar >= 1;";
        append_to_proof_log(line.str(), ProofPart::DERIVATION);
    }


    void ProofLog::op_implies_min_cost_delta(int op_id){
        ostringstream line;
        line << "rup: ~action" << op_id << " + min_cost_delta >= 1;";
        append_to_proof_log(line.str(), ProofPart::DERIVATION);
    }


    void ProofLog::reify_min_cost_delta(int min_cost){
        ostringstream line;
        line << "red: ~min_cost_delta + delta_geq_" << min_cost << ">= 1; min_cost_delta -> 0";
        append_to_proof_log(line.str(), ProofPart::REIFICATION);
        line << "red: min_cost_delta + ~delta_geq_" << min_cost << ">= 1; min_cost_delta -> 1";
        append_to_proof_log(line.str(), ProofPart::REIFICATION);
    }
}