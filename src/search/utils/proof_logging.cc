#include "proof_logging.h"

#include "logging.h"

#include <cassert>
#include <fstream>
#include <iostream>
#include <regex>
#include <string>

#include <cstdio>

using namespace std;


int proof_log_var_count;
int proof_log_max_cost_bits;

namespace utils {

// TODOprooflog where should this live?
int ceil_log_2(int val) { // https://stackoverflow.com/a/994647/27389055
    assert(val > 0); // Invalid input
    val = val + val; // rounding up
    if (val == 1) return 0;
    unsigned int ret = 0;
    while (val > 1) {
        val >>= 1;
        ret++;
    }
    return ret;
}

void ProofLog::clear_opb()
{
    string file_name = "opb.opb";
    
    // open the file without append mode to clear it
    ofstream file(file_name);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for clearing." << endl;
        return;
    }
    file << "";
    file.close();
}

// does no line break as default
void ProofLog::append_to_opb(const string &s)
{
    string file_name = "opb.opb";

    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << s;
    file.close();
}

// does line break on its own
void ProofLog::append_to_proof_log(const string &line, ProofPart proof_part, const string &comment)
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
    case ProofPart::BUDGET:
        {
            file_name = "budget.prooflog"; 
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
    if (!comment.empty()){
        file << "% ^ " <<comment << endl;
    }
    file.close();
}

void ProofLog::append_comment_to_proof_log(const std::string& comment) {
    append_to_proof_log("%"+comment, ProofPart::REIFICATION);
    append_to_proof_log("%"+comment, ProofPart::DERIVATION);
}

void ProofLog::append_to_proof_file(const string &line, const string &file_name, string)
{
    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << line;
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

void bireif_vector_sum(string reif_var, vector<string> vectors, int bound, string comment="bireif_vector_sum") {
    ProofLog::append_to_proof_log("% v " + comment, ProofPart::REIFICATION);

        int bits = ProofLog::get_proof_log_bits();
        int maxint = (1 << bits) - 1;
        ostringstream r_reif;
        ostringstream l_reif;
        assert(reif_var.size() > 0);
        r_reif << "@" << reif_var << "_Rreif " << " red ";
        l_reif << "@" << reif_var << "_Lreif " << " red ";
        for (string vector : vectors){
            bool negative = vector[0] == '-';
            string vec_name_aux = (negative ? vector.substr(1,vector.length()) : vector);
            bool is_dynamic = vec_name_aux.back() == ':' || vec_name_aux.back() == '.';
            string postfix = (is_dynamic ? vec_name_aux.substr(vec_name_aux.length()-1,vec_name_aux.length()) : "");
            string vec_name = (is_dynamic ? vec_name_aux.substr(0,vec_name_aux.length()-1) : vec_name_aux);
            if (negative){
                assert(bound+maxint >= bound);
                bound += maxint;
            }
            assert(vec_name.size()>0);
            for (int i = 0; i < bits; ++i) {
                r_reif << " " << (1 << i) << " " << (negative ? "~" : " ") << vec_name << "_" << i << postfix << " ";  
                l_reif << " " << (1 << i) << " " << (negative ? " " : "~") << vec_name << "_" << i << postfix << " ";  
            }
        }
        int A = bound;
        int M = (vectors.size()*maxint);

        r_reif <<   A   << " ~" << reif_var << " >= " <<   A   << " : " << reif_var << " -> 0 ;";
        l_reif << M-A+1 << "  " << reif_var << " >= " << M-A+1 << " : " << reif_var << " -> 1 ;";

        ProofLog::append_to_proof_log(r_reif.str() , ProofPart::REIFICATION, comment);
        ProofLog::append_to_proof_log(l_reif.str() , ProofPart::REIFICATION, comment);
}

string format(string var) {
    return (var[0] == '~' ? var : " " + var);
}

string negate(string var) {
    return (var[0] == '~' ? var.substr(1,var.length()) : "~" + var);
}


string ProofLog::put_prime(bool is_prime){
    return (is_prime ? "_t1" : "_t0");
}


string ProofLog::veripbfy(int x) {
    if (x < 0) {
        return "neg" + std::to_string(-x);
    }
    return std::to_string(x);
}



void bireif_flat_formula(string reif_var, vector<string> elements, bool is_disjunction, string comment="bireif_formla") {
    ProofLog::append_to_proof_log("% v "+comment, ProofPart::REIFICATION);
    ostringstream r_reif, l_reif;
    assert(reif_var.size() > 0);
    r_reif << "@" << reif_var << "_Rreif " << " red ";
    l_reif << "@" << reif_var << "_Lreif " << " red ";
    for (string element : elements) {
        r_reif << " 1 " << format(       utils::ProofLog::strips_name_to_veripb_name(element) )         << " ";
        l_reif << " 1 " << format(negate(utils::ProofLog::strips_name_to_veripb_name(element))) << " ";
    }
    int A = elements.size();
    r_reif << " " << (is_disjunction ? 1 : A) << " ~" << reif_var << " >= " << (is_disjunction ? 1 : A) << " : " << reif_var << " -> 0 ;";
    l_reif << " " << (is_disjunction ? A : 1) << "  " << reif_var << " >= " << (is_disjunction ? A : 1) << " : " << reif_var << " -> 1 ;";
    ProofLog::append_to_proof_log(r_reif.str() , ProofPart::REIFICATION, comment);
    ProofLog::append_to_proof_log(l_reif.str() , ProofPart::REIFICATION, comment);
}

void ProofLog::bireif_conjunction(string reif_var, vector<string> conjuncts, string comment="bireif_conjunction") {
    bireif_flat_formula(utils::ProofLog::strips_name_to_veripb_name(reif_var), conjuncts, false, comment);
}

void ProofLog::bireif_disjunction(string reif_var, vector<string> disjuncts, string comment="bireif_disjunction") {
    bireif_flat_formula(utils::ProofLog::strips_name_to_veripb_name(reif_var), disjuncts, true, comment);
}

void append_file_to_proof_log(string file_2, ProofPart proof_part){
    string file_1;
    switch (proof_part)
    {
    case ProofPart::REIFICATION:
        {
            file_1= "reifications.prooflog";
            break;
        }
    case ProofPart::DERIVATION:
        {
            file_1 = "derivations.prooflog";
            break;
        }
    case ProofPart::BUDGET:
        {
            file_1 = "budget.prooflog"; 
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

    std::ifstream in(file_2);
    std::ofstream out(file_1, std::ios_base::out | std::ios_base::app);

    for (std::string str; std::getline(in, str); )
    {
        out << "\n\n%%%%% APPEND FILE '" << file_2 << "' TO PROOF LOG\n\n" << str << endl << endl;
    }
}

void ProofLog::append_files_to_proof_log(std::vector<std::string> files, ProofPart proof_part){
    for (string file : files) {
        append_file_to_proof_log(file, proof_part);
    }
}

void add_spent_geq_x_bireification_aux(const int x, bool is_prime, bool balance, string comment){
    string e = (is_prime ? "e_t1" : "e_t0");
    ostringstream reif_var;
    reif_var << (balance ? "balance_geq_" : "spent_geq_") << utils::ProofLog::veripbfy(x) << utils::ProofLog::put_prime(is_prime);
    int bits = ProofLog::get_proof_log_bits();
    int maxint = (1 << bits) -1;
    assert(x<maxint);
    bireif_vector_sum(reif_var.str(), (balance ? vector<string>{"b", "-"+e} : vector<string>{e}), x, comment);

    // bireif of inverse statement  b_leq_2 iff ~b_geq_3    sp_geq_2 iff ~sp_leq_1
    ostringstream reif_var2, conjunct;
    reif_var2 << (balance ? "balance_leq_" : "spend_leq_") << utils::ProofLog::veripbfy(x - 1) << utils::ProofLog::put_prime(is_prime);
    conjunct << "~" << (balance ? "balance_geq_" : "spend_geq_") << utils::ProofLog::veripbfy(x) << utils::ProofLog::put_prime(is_prime);
    ProofLog::bireif_conjunction(reif_var2.str(), vector<string>({conjunct.str()}), comment);

}

void ProofLog::bireif_balance_leq(int x, string comment) {
    add_spent_geq_x_bireification_aux(x+1, false, true, comment);
    add_spent_geq_x_bireification_aux(x+1, true, true, comment);

}

void ProofLog::add_spent_geq_x_bireification(const int x, string comment){
    add_spent_geq_x_bireification_aux(x, false, false, comment);
    add_spent_geq_x_bireification_aux(x, true, false, comment);
}

void ProofLog::add_balance_leq_x_bireification(const int x, string comment){
    add_spent_geq_x_bireification_aux(x, false, true, comment);
    add_spent_geq_x_bireification_aux(x, true, true, comment);
}


int get_ith_bit_of_x(int i, int x) {
     return (x & (1 << i)) != 0;
}

void ProofLog::finalize_lemmas(int optimal_cost, string comment) {

    // TODOprooflogging remove this:
        append_to_proof_log("% ensure non empty REIF file", ProofPart::REIFICATION);

    append_to_proof_log("% finalize:\n", ProofPart::BUDGET);
    int bits = get_proof_log_bits();
    ostringstream r_budget;
    ostringstream l_budget;
    r_budget << "% varcount: " << proof_log_var_count << endl << "% max cost bits: " << proof_log_max_cost_bits << endl << endl;
    r_budget << "@budget_Rreif  red ";
    l_budget << "@budget_Lreif  red ";
    for (int i = bits - 1; i >= 0; --i) {
        r_budget << " " << (1 << i) << " b_" << i << " ";
        l_budget << " " << (1 << i) << " ~b_" << i << " ";
    }
    r_budget << " >= " << optimal_cost << " : ";
    l_budget << " >= " << (1 << bits)-optimal_cost-1 << " : ";
    for (int i = bits - 1; i >= 0; --i) {
        r_budget << " " << " b_" << i << " -> " << get_ith_bit_of_x(i, optimal_cost);
        l_budget << " " << " b_" << i << " -> " << get_ith_bit_of_x(i, optimal_cost);
    }
    r_budget << " ;";
    l_budget << " ;";
    append_to_proof_log(r_budget.str(), ProofPart::BUDGET, comment);
    append_to_proof_log(l_budget.str(), ProofPart::BUDGET, comment);

    // ensure to define spent_geq_optimal_cost and balance_leq_0
    add_spent_geq_x_bireification_aux(optimal_cost, false, false, comment);
    add_spent_geq_x_bireification_aux(optimal_cost, true, false, comment);
    add_spent_geq_x_bireification_aux(0, false, true, comment);
    add_spent_geq_x_bireification_aux(0, true, true, comment);
    // define spent_geq_optimal_cost+1 and balance_leq_-1
    add_spent_geq_x_bireification_aux(optimal_cost+1, false, false, comment);
    add_spent_geq_x_bireification_aux(optimal_cost+1, true, false, comment);
    add_spent_geq_x_bireification_aux(-1, false, true, comment);
    add_spent_geq_x_bireification_aux(-1, true, true, comment);



    ostringstream spent_all;
    spent_all << "pol  @budget_Lreif  @balance_leq_0_t0_Lreif " << (1 << get_proof_log_bits()) << " * +  @spent_geq_" << optimal_cost << "_t0_Rreif + @balance_geq_1_t0_Rreif + ;" << "\n % proof_logging.cc finalize_lemmas"
        << endl << "% sanity check (with rup instead of e because i dont want to devide by the correct vaule i dont bother to compute and would be to large to just cover all cases)" << endl
        << "rup 1 ~spent_geq_" << optimal_cost << "_t0  1 balance_leq_0_t0  >= 1 : -1 ;" << "\n % " << comment;
    append_to_proof_log(spent_all.str(), ProofPart::REIFICATION, "TODO: should belong to start of derivation."); //TODOprooflogging this should belong at the start of derivations

    ostringstream spent_even_more;
    spent_even_more << "pol  @budget_Lreif  @balance_leq_neg1_t0_Lreif " << (1 << get_proof_log_bits()) << " * +  @spent_geq_" << optimal_cost+1 << "_t0_Rreif + @balance_geq_0_t0_Rreif + ;" << "\n % proof_logging.cc finalize_lemmas"
        << endl << "% sanity check (with rup instead of e because i dont want to devide by the correct vaule i dont bother to compute and would be to large to just cover all cases)" << endl 
        << "rup 1 ~spent_geq_" << optimal_cost+1 << "_t0  1 balance_leq_neg1_t0  >= 1 : -1 ;" << "\n % proof_logging.cc finalize_lemmas";
    append_to_proof_log(spent_even_more.str(), ProofPart::REIFICATION); //TODOprooflogging this should belong at the start of derivations

    ostringstream sanity;
    sanity << "% help for sanity check" << endl;
    sanity << "pol  @balance_leq_neg1_t0_Rreif " << (1 << get_proof_log_bits()) << " *  @balance_leq_0_t0_Lreif " << (1 << get_proof_log_bits()) << " *  + @balance_geq_0_t0_Lreif @balance_geq_1_t0_Rreif + + ;" << "\n % proof_logging.cc finalize_lemmas" << endl;
    sanity << "rup  1 ~balance_leq_neg1_t0  1 balance_leq_0_t0  >= 1 : -1 ;" << "\n % proof_logging.cc finalize_lemmas" << endl;
    sanity << "pol  @spent_geq_" << optimal_cost << "_t0_Lreif  @spent_geq_" << optimal_cost+1 << "_t0_Rreif  + ;" << "\n % proof_logging.cc finalize_lemmas" << endl;
    sanity << "rup  1 spent_geq_" << optimal_cost << "_t0  1 ~spent_geq_" << optimal_cost+1 << "_t0 >= 1 : -1 ;" << "\n % proof_logging.cc finalize_lemmas" << endl;
    append_to_proof_log(sanity.str(), ProofPart::REIFICATION); //TODOprooflogging this should belong at the start of derivations

    ostringstream lemmas;
    lemmas << endl << endl <<"% entry lemma balance" << endl
        << "@lem3  rup  1 ~s_init_t0  1 balance_leq_" << optimal_cost << "_t0  1 invar_t0  >= 1 ;" << "\n % proof_logging.cc finalize_lemmas" << endl
        << "% goal lemma balance" << endl
        << "@lem4  rup  1 ~goal_t0  1 balance_leq_" << 0 << "_t0  1 ~invar_t0  >= 1 ;" << "\n % proof_logging.cc finalize_lemmas" << endl
        << "% transition lemma balance" << endl
        << "@lem7  rup  1 ~invar_t0  1 ~transition  1 invar_t1  >= 1 ; " << "\n % proof_logging.cc finalize_lemmas" <<endl
        << endl << endl <<"% entry lemma spent" << endl 
        << "rup  1 ~s_init_t0  1 spent_geq_1_t0  1 invar_t0  >= 1 ;" << "\n % proof_logging.cc finalize_lemmas" << endl
        << "% goal lemma spent" << endl
        << "rup  1 ~goal_t0  1 spent_geq_" << optimal_cost << "_t0  1 ~invar_t0  >= 1 ;" << "\n % proof_logging.cc finalize_lemmas" << endl
        << "% transition lemma spent" << endl
        << "rup  1 ~invar_t0  1 ~transition  1 invar_t1  >= 1 ; " << "\n % proof_logging.cc finalize_lemmas" <<endl
        << "output NONE ;" << endl
        << "conclusion NONE ;" << endl
        << "end pseudo-Boolean proof ;" << endl;
    append_to_proof_log(lemmas.str(), ProofPart::DERIVATION);
}

int MAX_BIT_BOUNDARY = 30;

int ProofLog::get_proof_log_maxint() {
    return (1 << get_proof_log_bits())-1;
}


int ProofLog::get_proof_log_bits() {
    // TODOprooflogging make this pivate, others should ask for maxint directly.
    return std::min(1+proof_log_max_cost_bits+proof_log_var_count, MAX_BIT_BOUNDARY);
// TODOprooflogging expreimental added +1 ... there might be some weirdness when this is exactly 2**x (+-1)  ? :( ?

    // here we will need more bits once we talk about infinity
    // it would be nice to not do this but it would require arbitrary size integer operations
}

bool check_first_line(const std::string& filename, const std::string& searchString) {
    std::ifstream file(filename);
    
    if (!file.is_open()) {
        throw std::runtime_error("Unable to open file: " + filename);
    }
    
    std::string firstLine;
    if (!std::getline(file, firstLine)) {
        throw std::runtime_error("File is empty");
    }
    
    return firstLine.find(searchString) != std::string::npos;
}

bool ProofLog::is_meta_file(string meta_file_name) {
	return check_first_line(meta_file_name, "%META");
}

vector<string> ProofLog::get_subfiles(string meta_file_name) {
  utils::g_log << "get subfiles of " << meta_file_name << "." << endl;
	std::vector<std::string> subfiles;
    std::ifstream file(meta_file_name);
    
    if (!file.is_open()) {
        throw std::runtime_error("Unable to open file: " + meta_file_name);
    }
    
    bool first = true;
    std::string line;
    while (std::getline(file, line)) {
        if (first) {
	   first = false;
	} else {
           subfiles.push_back(line);
	}
    }
    
    return subfiles;
}

void ProofLog::merge_proof_log_files(string meta_file_name) {
	std::vector<std::string> subfiles;
        if (is_meta_file(meta_file_name)) {
            vector<string> sub_files = get_subfiles(meta_file_name);
            for (string sub_file : sub_files) {
                merge_proof_log_files(sub_file);
            }
        } else {
	    append_to_plan_pbp(meta_file_name);
        }
}

void ProofLog::create_plan_pbp(){
    string file_name = "plan.pbp";
    ofstream file(
        file_name
        , ios_base::trunc);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file << "pseudo-Boolean proof version 3.0\n\n%from create_plan_pbp()\n";
    file.close();
}

void ProofLog::finalize_plan_pbp(){
    string file_name = "plan.pbp";
    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    file.close();
}

int ProofLog::runCommand(const std::string& command, const std::string& searchString) {
  utils::g_log << "Verify with command: '" << command << "'." << endl;
    try {
        // Create pipe between system command and this process
        string cmd = command + " 2>&1";  // Capture both stdout and stderr
        FILE* pf = popen(cmd.c_str(), "r");

        if (!pf) {
            throw std::runtime_error("Failed to open pipe to command");
        }

        // Extract output of command
        std::ostringstream oss;
        char buffer[128];
        while (fgets(buffer, 128, pf)) {
            std::string line(buffer);

            // Display output immediately
            utils::g_log << line << endl;

            // Add to stored output for checking
            oss << line;
        }

	// Close pipe
        pclose(pf);

        // Get command output as string
        std::string output = oss.str();

        // Check if output contains the search string
        if (output.find(searchString) == std::string::npos) {
            throw std::runtime_error("Search string not found in command output");
        }

        // Return success (0)
        utils::g_log << "Verification ended." << endl;
        return 0;

    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << '\n';
        return -1;
    }
}

void ProofLog::append_to_plan_pbp(std::string sourceFile) {
    string destinationFile = "plan.pbp";
    assert(0!=destinationFile.compare(sourceFile));
    std::ifstream source(sourceFile);
    std::ofstream dest(destinationFile, std::ios::app);

    if (!source.is_open()) {
        throw std::runtime_error("Unable to open source file: " + sourceFile);
    }

    if (!dest.is_open()) {
        throw std::runtime_error("Unable to open destination file: " + destinationFile);
    }
    
    std::string line;
    while (std::getline(source, line)) {
        dest << line << '\n';
    }
}

void ProofLog::make_proof_file(string name){
    string file_name = name+".prooflog";
    ofstream file(
        file_name
        , ios_base::app);
    if (!file.is_open()) {
        cerr << "Error opening " << file_name << " for appending." << endl;
        return;
    }
    //file << "* " + name + ".prooflog";
    file.close();
}

// WARNING: this function has to be syncronized with same named one in the python part.
string ProofLog::strips_name_to_veripb_name(const string& strips_name) {
    regex pattern("[a-zA-Z0-9\\[\\]\\{\\}\\^\\-\\~_]");
    string veripb_name;
    for (char c : strips_name) {
        if (! regex_search(string(1, c), pattern)) {
            veripb_name += "[ASCII" + to_string(static_cast<int>(c)) + "]";
            //veripb_name += "_";
        } else {
            veripb_name += c;
        }
    }
    
    return veripb_name;
}
}
