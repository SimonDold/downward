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
    case ProofPart::INVARIANT:
        {
            file_name = "invariant.prooflog"; 
            /*
                it is not truly THE invariant but all needed (and some not needed) reifications that build the invariant.
                The invariant is in the file invarinat_right.prooflog and invariant_left.prooflog
            */
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

// TODOprooflog remove 4fold code duplication 

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

void ProofLog::append_to_invariant_prime_right(const string& summand) {
    string file_name = "invariant_prime_right.prooflog";
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

void ProofLog::append_to_invariant_prime_left(const string& summand) {
    string file_name = "invariant_prime_left.prooflog";
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




void ProofLog::add_spent_geq_x_bireification(const int x){
    
    int bits = 8; // TODOprooflog this is hardcoded atm :(
    
    ostringstream r_line;
    ostringstream l_line;
    r_line << "@spent_geq_" << x << "_Rreif ";
    l_line << "@spent_geq_" << x << "_Lreif ";
    for (int i = bits - 1; i >= 0; --i) {
        r_line << " " << (1 << i) << " c_" << i << " ";
        l_line << " " << (1 << i) << " ~c_" << i << " ";
    }
    r_line << x << " ~spent_geq_" << x << "  >= " << x;
    l_line << ((1 << bits) - x) << " spent_geq_" << x << "  >= " << ((1 << bits) - x);

    append_to_proof_log(r_line.str(), ProofPart::INVARIANT);
    append_to_proof_log(l_line.str(), ProofPart::INVARIANT);

    ostringstream r_prime_line;
    ostringstream l_prime_line;
    r_prime_line << "@prime^spent_geq_" << x << "_Rreif ";
    l_prime_line << "@prime^spent_geq_" << x << "_Lreif ";
    for (int i = bits - 1; i >= 0; --i) {
        r_prime_line << " " << (1 << i) << " prime^c_" << i << " ";
        l_prime_line << " " << (1 << i) << " ~prime^c_" << i << " ";
    }
    r_prime_line << x << " ~prime^spent_geq_" << x << "  >= " << x;
    l_prime_line << ((1 << bits) - x) << " prime^spent_geq_" << x << "  >= " << ((1 << bits) - x);

    append_to_proof_log(r_prime_line.str(), ProofPart::INVARIANT);
    append_to_proof_log(l_prime_line.str(), ProofPart::INVARIANT);

    ostringstream derivation_line;
    derivation_line << endl << "pol  @spent_geq_" << x << "_Rreif  @prime^spent_geq_" << x << "_Lreif  @delta_cost_geq_MIN  +  + " << (1 << bits) << " d ;";
    append_to_proof_log(derivation_line.str(), ProofPart::DERIVATION);
}

void ProofLog::finalize_lemmas(int optimal_cost) {
    ostringstream lemmas;
    lemmas << endl << endl <<"* entry lemmas" << endl
        << "rup  1 ~s_init  1 spent_geq_1  1 invar  >= 1 ;" << endl
        << "* goal lemma" << endl
        << "rup  1 ~goal  1 spent_geq_" << optimal_cost << "  ~invar  >= 1 ;" << endl
        << "* transition lemma" << endl
        << "rup  1 ~invar  1 ~transition  1 prime^invar  >= 1 ; " <<endl;
    append_to_proof_log(lemmas.str(), ProofPart::DERIVATION);
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