#include "proof_logging.h"

#include <fstream>
#include <iostream>
#include <regex>

using namespace std;

namespace utils {

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
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << line << endl;
    file.close();
}

void ProofLog::append_to_invariant_right(const string& summand) {
    string file_name = "invariant_right.prooflog";
    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << summand;
    file.close();
}

void ProofLog::append_to_invariant_left(const string& summand) {
    string file_name = "invariant_left.prooflog";
    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << summand;
    file.close();
}

// WARNING: this function has to be syncronized with same named one in the python part.
string ProofLog::strips_name_to_veripb_name(const string& strips_name) {
    regex pattern("[a-zA-Z0-9\\[\\]\\{\\^\\-]");
    string veripb_name;
    for (char c : strips_name) {
        if (! regex_search(string(1, c), pattern)) {
            //veripb_name += "[ASCII" + to_string(static_cast<int>(c)) + "]";
            veripb_name += "_";
        } else {
            veripb_name += c;
        }
    }
    
    return veripb_name;
}
}