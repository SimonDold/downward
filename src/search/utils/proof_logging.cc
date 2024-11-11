#include "proof_logging.h"

#include <fstream>
#include <iostream>
#include <sstream>

using namespace std;

namespace utils {

ProofLog::ProofLog(const string &file_name)
    :
    file_name(file_name)
          {
            std::ofstream file(file_name);
            if (!file.is_open())
            {
                std::cerr << "Failed to open file: " << file_name << std::endl;
            }
            file.close();
    }

void ProofLog::append_to_proof_log(const string &line)
{
    std::ofstream file(file_name, std::ios_base::app);
    if (!file.is_open()) {
        std::cerr << "Error opening file for appending." << std::endl;
        return;
    }
    file << line << std::endl;
    file.close();
}

    void ProofLog::add_state_reification(StateID id, State s){
        s.unpack();
        ostringstream line;
        line << "R-reification r" << id << ": ~r" << id;
        auto x = s.get_unpacked_values();
        for (unsigned int i = 0; i < x.size(); ++i) {
            line << " + v" << i << "_"<< x[i];
        }
        line << " >= " << x.size() << ";";
        append_to_proof_log(line.str());
    }
}