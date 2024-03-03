#! /usr/bin/env python3


import argparse
import re
import subprocess
import sys

CONTRUCTOR_REGEX = r"\b(\w+)(?:\s*::\s*\1\b)+"
CREATE_COMPONENT_REGEX = r"(^|\s|\W)create_component"
C_VAR_PATTERN = r'[^a-zA-Z0-9_]' # overapproximation
def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("cc_file", nargs="+")
    return parser.parse_args()

def extract_cpp_class(input_string):
    pattern = r'<(.*?)>'
    match = re.search(pattern, input_string)
    assert match
    return match.group(1)


def get_constructor_parameters(cc_file, class_name):
    with open(cc_file, 'r') as file:
        content = file.read()
    pattern = rf'{class_name}\s*\((.*?)\)'
    match = re.search(pattern, content, re.DOTALL)

    if match:
        parameters = match.group(1).strip()
        return (True, parameters)
    else:
        return (False, "")

def extract_balanced_parentheses(s, feature_name):
    position = s.find(feature_name + "(")
    assert position != -1
    s = s[position + len(feature_name) + 1::]
    s = s.split(')\\n-')[0]
    return s

def remove_balanced_brackets(s):
    stack = []
    result = []
    for c in s:
        if c == '[':
            stack.append(c)
        elif c == ']':
            if stack and stack[-1] == '[':
                stack.pop()
            else:
                result.append(c)
        elif not stack:
            result.append(c)
    return ''.join(result)

def extract_feature_name_and_cpp_class(cc_file, args, num):
    source_without_comments = subprocess.check_output(
        ["gcc", "-fpreprocessed", "-dD", "-E", cc_file]).decode("utf-8")

    name_pattern = r'TypedFeature\("([^"]*)"\)'
    class_pattern = r'TypedFeature<(.*?)>'

    feature_names = []
    class_names = []
    other_namespaces = []
    feature_error_msgs = []
    class_error_msgs = []
    for line in source_without_comments.splitlines():
        if re.search(name_pattern, line):
            feature_name = re.search(name_pattern, line).group(1)
            feature_error_msg = "feature_name: " + feature_name + "\n"
            feature_names.append(feature_name)
            feature_error_msgs.append(feature_error_msg)

        if re.search(class_pattern, line):
            feature_class = re.search(class_pattern, line).group(1)
            class_name = feature_class.split()[-1].split("::")[-1]
            other_namespace = len(feature_class.split()[-1].split("::")) == 2
            class_error_msg = "class_name: " + class_name + "\n"
            class_names.append(class_name)
            other_namespaces.append(other_namespace)
            class_error_msgs.append(class_error_msg)
    return feature_names[num], class_names[num], other_namespaces[num], feature_error_msgs[num] + class_error_msgs[num]

def get_feature_parameters(feature_name):
    doc_Entry = subprocess.run(["./../../builds/release/bin/downward", "--help", "--txt2tags", "{}".format(feature_name)], stdout=subprocess.PIPE).stdout
    doc_Entry = str(doc_Entry)
    in_parenthesis = extract_balanced_parentheses(doc_Entry, feature_name)
    in_parenthesis = remove_balanced_brackets(in_parenthesis)
    result = re.sub(r'=.*?,', ',', in_parenthesis + ",").split()
    return result

def get_cpp_class_parameters(class_name, other_namespace, cc_file, args):
    found_in_file, parameters = get_constructor_parameters(cc_file, class_name)
    if not found_in_file:
        # check in all files
        for cc_file2 in args.cc_file:
            found_in_file, parameters = get_constructor_parameters(cc_file2, class_name)
            if found_in_file:
                break

    if found_in_file:
        parameters = parameters.replace("\n", "") + ","
        parameters = parameters.split()
        parameters = [word for word in parameters if "," in word]
        parameters = [re.sub(C_VAR_PATTERN, '', word) + "," for word in parameters]
        return parameters
    else:
        # assume default constructor
        return [","]

def get_create_component_lines(cc_file):
    source_without_comments = subprocess.check_output(
        ["gcc", "-fpreprocessed", "-dD", "-E", cc_file]).decode("utf-8")
    lines = []
    for line in source_without_comments.splitlines():
        if re.search(CREATE_COMPONENT_REGEX, line):
            lines.append(line.strip())
    return lines

def compare_component_parameters(cc_file, args):
    found_error = False
    error_msg = ""
    create_component_lines = get_create_component_lines(cc_file)
    if not create_component_lines == []:
        for i, create_component_line in enumerate(create_component_lines):
            feature_name, cpp_class, other_namespace, extracted_error_msg = extract_feature_name_and_cpp_class(cc_file, args, i)
            error_msg += "\n\n=====================================\n= = = " + cpp_class + " = = =\n"
            error_msg += extracted_error_msg + "\n"
            feature_parameters = get_feature_parameters(feature_name)

            error_msg += "== FEATURE PARAMETERS '" + feature_name + "'==\n"
            error_msg += str(feature_parameters) + "\n"

            cpp_class_parameters = get_cpp_class_parameters(cpp_class, other_namespace, cc_file, args)

            error_msg += "== CLASS PARAMETERS '" + cpp_class + "'==\n"
            error_msg += str(cpp_class_parameters) + "\n"

            if feature_parameters != cpp_class_parameters:
                found_error = True
                if not len(feature_parameters) == len(cpp_class_parameters):
                    error_msg += "Wrong sizes\n"
                for i in range(min(len(feature_parameters), len(cpp_class_parameters))):
                    if feature_parameters[i] != cpp_class_parameters[i]:
                        error_msg += feature_parameters[i] + " =/= " + cpp_class_parameters[i] + "\n"
                error_msg += cc_file + "\n"

    return found_error, error_msg

def main():
    args = parse_args()
    errors = []
    for cc_file in args.cc_file:
        found_error, error = compare_component_parameters(cc_file, args)
        if found_error:
            errors.append(error)
    if errors:
        print("#########################################################")
        print("#########################################################")
        print("#########################################################")
        print("#########################################################")
        print("#########################################################")
        print(".: ERRORS :.")
        for error in errors:
            print(error)
        sys.exit(1)


if __name__ == "__main__":
    main()
