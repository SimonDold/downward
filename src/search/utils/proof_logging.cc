#include "proof_logging.h"

#include <fstream>
#include <iostream>
#include <sstream>

using namespace std;

namespace utils {

ProofLog::ProofLog()
    {
    }

void ProofLog::append_to_proof_log(const string &line, ProofPart proof_part)
{
    string file_name;
    switch (proof_part)
    {
    case ProofPart::REIFICATION:
        {
            file_name = "reifications.prooflog";
            break;
        }
    case ProofPart::DERIVATION:
        {
            file_name = "derivations.prooflog";
            break;
        }
    default:
        cerr << "Error: Not clear where to add." << endl;
        break;
    }

    ofstream file(
        file_name
        , std::ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << line << std::endl;
    file.close();
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