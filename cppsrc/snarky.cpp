#include <fstream>
#include <iostream>
#include <sstream>

#include <getopt.h>
#include <stdio.h>

#include <libsnark/common/default_types/r1cs_ppzksnark_pp.hpp>
#include <libsnark/relations/variable.hpp>
#include <libsnark/relations/constraint_satisfaction_problems/r1cs/r1cs.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>

using namespace std;
using namespace libsnark;

// These extra reading functions are necessary because we want to
// express constraints from an external constraint generator mod p and
// libsnark wants to print numbers in Montgomery space mod p when it's
// not in debug mode. Running in debug mode presents alternative
// headaches.

void read_lc_decimal(istream& constraintStream, linear_combination<Fr<default_ec_pp> > *lc) 
{
    size_t num_terms;

    /* [NOTE: Linear Combination Serialization]
       The serialization of a linear combination is:
       <num-terms> //number of terms in the polynomial
       <variable-index> //a variable index (0 is reserved for the constant term)
       <variable-coeff> 
     */
    lc->terms.clear();
    constraintStream >> num_terms;
    // cout << "num. terms: " << num_terms << "\n";
    consume_newline(constraintStream);

    lc->terms.reserve(num_terms);
    for (size_t i = 0; i < num_terms; ++i) {
        linear_term<Fr<default_ec_pp> > lt;
        constraintStream >> lt.index; // size_t
	// cout << "var. index: " << lt.index << "\n";
        consume_newline(constraintStream);
        // lt.coeff is a Fr<default_ec_pp>, which I _believe_ is a
        // bn128_Fr, which is definitely an Fp_model<bn128_r_limbs,bn128_modulus_r>
        constraintStream >> lt.coeff.mont_repr;
	// cout << "coeff. before reduction: " << lt.coeff.mont_repr << "\n";
        // Reduce to Montgomery Space, as per method in algebra/fields/fp.tcc
        lt.coeff.mul_reduce(Fr<default_ec_pp>::Rsquared);
	// cout << "coeff. after reduction: " << lt.coeff.mont_repr << "\n";
        consume_OUTPUT_NEWLINE(constraintStream);
        lc->terms.emplace_back(lt);
    }
}

void read_cs_decimal(istream& constraintStream, r1cs_constraint_system<Fr<default_ec_pp> > &cs) 
{
    size_t primary_input_size;
    size_t auxiliary_input_size;

    /* [NOTE: R1CS Serialization]
       The serialization format for the R1CS header is:
         <primary_input_size> //num. input variables 
         <auxiliary_input_size> //num. add'l witness variables
         <num_constraints> 
	 for each constraint in [0..<num_constraints>-1]:
  	   <serialization-of-A-polynomial>
	   <serialization-of-B-polynomial>
	   <serialization-of-C-polynomial>
     */
    constraintStream >> primary_input_size; 
    // cout << "primary input size: " << primary_input_size << "\n";
    cs.primary_input_size = primary_input_size;
    constraintStream >> auxiliary_input_size;
    // cout << "auxiliary input size: " << auxiliary_input_size << "\n";
    cs.auxiliary_input_size = auxiliary_input_size;

    cs.constraints.clear();
    size_t num_constraints;
    constraintStream >> num_constraints;
    // cout << "num. constraints: " << num_constraints << "\n";
    consume_newline(constraintStream);

    cs.constraints.reserve(num_constraints);
    for (size_t i = 0; i < num_constraints; ++i) {
        linear_combination<Fr<default_ec_pp> > A, B, C;
	// cout << "A:\n";
        read_lc_decimal(constraintStream, &A);
	// cout << "B:\n";
        read_lc_decimal(constraintStream, &B);
	// cout << "C:\n";
        read_lc_decimal(constraintStream, &C);
        cs.add_constraint(r1cs_constraint<Fr<default_ec_pp> >(A, B, C));
    }
}

void generateKeys(istream& constraintStream, ostream& pkStream, ostream& vkStream) 
{
    r1cs_constraint_system<Fr<default_ec_pp> > cs;
    read_cs_decimal(constraintStream, cs);
    // cout << "reserialization of constraint system:\n";
    // cout << cs;
    r1cs_ppzksnark_keypair<default_ec_pp> keypair = r1cs_ppzksnark_generator<default_ec_pp>(cs);
    // Generator writes out keys
    pkStream << keypair.pk;
    vkStream << keypair.vk;
}

void readVariableAssignment(istream& stream, r1cs_variable_assignment<Fr<default_ec_pp> >& assgn)
{
    /* [NOTE: Variable Assignments Serialization]
       <coeff_1>
       <coeff_2>
       ...
       <coeff_n>EOF
     */
    for (string line; getline(stream, line);)
    {
        linear_term<Fr<default_ec_pp> > lt;
        stringstream(line) >> lt.coeff.mont_repr;
	// cout << "coeff. before reduction: " << lt.coeff.mont_repr << "\n";

        // Reduce to Montgomery Space, as per method in algebra/fields/fp.tcc
        lt.coeff.mul_reduce(Fr<default_ec_pp>::Rsquared);

        // cout << "pushing " << lt.coeff.mont_repr << "\n";
        assgn.push_back(lt.coeff);
    }
}
    
void generateProof(istream& pkStream, istream& inpStream, istream& witStream, ostream& pfStream) 
{
    //deserialize proving key
    r1cs_ppzksnark_proving_key<default_ec_pp> pk;
    pkStream >> pk;

    //deserialize input
    r1cs_variable_assignment<Fr<default_ec_pp> > input;
    readVariableAssignment(inpStream, input);
    // cout << "input is:\n" << input;

    //deserialize witness
    r1cs_variable_assignment<Fr<default_ec_pp> > witness;
    readVariableAssignment(witStream, witness);
    // cout << "witness is:\n" << witness;

    //generate proof
    r1cs_ppzksnark_proof<default_ec_pp> proof 
      = r1cs_ppzksnark_prover<default_ec_pp>(pk, input, witness);
    pfStream << proof;
}

bool verifyProof(istream& pfStream, istream& vkStream, istream& inpStream) 
{
    //deserialize proof
    r1cs_ppzksnark_proof<default_ec_pp> proof;
    pfStream >> proof;

    //deserialize verification key
    r1cs_ppzksnark_verification_key<default_ec_pp> vk;
    vkStream >> vk;

    //deserialize input strema
    r1cs_variable_assignment<Fr<default_ec_pp> > input;
    readVariableAssignment(inpStream, input);
    // cout << "input is:\n" << input;
    return r1cs_ppzksnark_verifier_strong_IC<default_ec_pp>(vk, input, proof);
}

void printFileError() 
{
    cout << "The wrong combination of files was specified for the requested functionality.\n";
}

void maybeCloseStream(fstream & fs) 
{
    if (fs.is_open()) {
        fs.close();
    }
}

int main(int argc, char* const* argv) 
{
    // declare option stuff
    static int generatorFlag, proverFlag, verifierFlag, reserializeFlag;
    static fstream csFileStream, provingKeyFileStream, verificationKeyFileStream, proofFileStream, witnessFileStream, inputFileStream;

    static struct option long_options[] = {
        {"generateKeys", no_argument, &generatorFlag, true},
        {"prove", no_argument, &proverFlag, true},
        {"verify", no_argument, &verifierFlag, true},
        {"reserialize", no_argument, &reserializeFlag, true},
        {"csFile", required_argument, 0, 'c'},
        {"proofFile", required_argument, 0, 'q'},
        {"provingKeyFile", required_argument, 0, 'f'},
        {"verificationKeyFile", required_argument, 0, 'k'},
        {"witnessFile", required_argument, 0, 'w'},
        {"inputFile", required_argument, 0, 'i'},
        {0,0,0,0}
    };

    //Initialize things like field modulus (IMPORTANT!)
    default_ec_pp::init_public_params();

    // Parse options and set up files.
    int option_char;
    int option_index;
    while (1) 
    {
        option_char = getopt_long(argc, argv, "gpvrq:f:k:w:i:", long_options, &option_index);
        if (option_char == -1) {
            break;
        }
        switch (option_char) {
        case 0:
            // Do nothing if we've set a flag already
            if (long_options[option_index].flag != 0)
                break;
        case 'c':
            csFileStream.open(optarg, fstream::in|fstream::out);
        case 'q':
            proofFileStream.open(optarg, fstream::in|fstream::out);
            break;
        case 'f':
            provingKeyFileStream.open(optarg, fstream::in|fstream::out);
            break;
        case 'k':
            verificationKeyFileStream.open(optarg, fstream::in|fstream::out);
            break;
        case 'w':
            witnessFileStream.open(optarg, fstream::in|fstream::out);
            break;
        case 'i':
            inputFileStream.open(optarg, fstream::in|fstream::out);
            break;
        case '?':
            // unknown option or missing required option
            // getopt_long prints a basic usage message
            break;
        }
    }
    if (reserializeFlag) {
        // TODO
    }
    if (generatorFlag) {
        if (csFileStream.is_open() && provingKeyFileStream.is_open() && verificationKeyFileStream.is_open()) {
            generateKeys(csFileStream, provingKeyFileStream, verificationKeyFileStream);
        } else {
            printFileError();
        }
    } else if (proverFlag) {
        if (provingKeyFileStream.is_open() && inputFileStream.is_open() && witnessFileStream.is_open() && proofFileStream.is_open()) {
            generateProof(provingKeyFileStream, inputFileStream, witnessFileStream, proofFileStream);
        } else {
            printFileError();
        }
    } else if (verifierFlag) {
        if (proofFileStream.is_open() && verificationKeyFileStream.is_open() && inputFileStream.is_open()) {
            bool ans = verifyProof(proofFileStream, verificationKeyFileStream, inputFileStream);
            if (ans) {
                cout << "Verification Succeeded!\n";
            } else {
                cout << "Verification Failed!\n";
            }
        } else {
            printFileError();
        }
    }
    
    // Release resources
    maybeCloseStream(csFileStream);
    maybeCloseStream(provingKeyFileStream);
    maybeCloseStream(verificationKeyFileStream);
    maybeCloseStream(proofFileStream);
    maybeCloseStream(witnessFileStream);
    maybeCloseStream(inputFileStream);
}
