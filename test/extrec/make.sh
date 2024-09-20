COMPILE_EXTREC="./build/mi-tmp compile --test --experimental-records"

TEST_LOCATION="test/extrec/"
TYPE_TEST_LOCATION="test/extrec/ill-typed/"

OUTPUT_LOCATION="test/extrec/out"

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

run_test() {
  input_file=$1
  file_prefix=${input_file%.*}
  set +e

  echo "--- $input_file ---"
  $COMPILE_EXTREC --output $OUTPUT_LOCATION/$file_prefix $TEST_LOCATION$input_file > /dev/null
  if [ $? -eq 0 ] 
  then
    printf "${GREEN}Compilation successful!\n${NC}"
    ./$OUTPUT_LOCATION/$file_prefix
    if [ $? -eq 0 ] 
    then 
      printf  "${GREEN}Test Passed}!\n${NC}"
    else 
      printf "${RED}Test or Execution Failed!\n${NC}"

    fi
    rm ./$OUTPUT_LOCATION/$file_prefix
  else
    printf "${RED}Compilation error!\n${NC}"
  fi
  set -e
}

run_all() {
  for test_file in $TEST_LOCATION*.mc 
  do
    relative_path=$(basename $test_file)
    # echo "$relative_path"
    # echo "$test_file"
    run_test $relative_path
  done
}

run_illtyped_test() {
  input_file=$1
  file_prefix=${input_file%.*}
  set +e

  echo "--- $input_file ---"
  $COMPILE_EXTREC --output $OUTPUT_LOCATION/$file_prefix $TYPE_TEST_LOCATION$input_file > /dev/null
  if [ $? -ne 0 ] 
  then
    printf "${GREEN}Type checking fialed as expected!\n${NC}"
  else
    printf "${RED}Compilation succeeded even though the program should not have been well-typed!\n${NC}"
  fi
  set -e
  rm -f ./$OUTPUT_LOCATION/$file_prefix
}

run_all_illtyped() {
    for test_file in $TYPE_TEST_LOCATION*.mc 
  do
    relative_path=$(basename $test_file)
    # echo "$relative_path"
    # echo "$test_file"
    run_illtyped_test $relative_path
  done
}

case $1 in 
  run-test)
    run_test "$2"
    ;;
  run-all)
    run_all
    run_all_illtyped
    ;;
  run-type-test)
    run_illtyped_test "$2"
    ;;
  run-all-type)
    run_all_illtyped
    ;;
  *)
    echo "Unknown command! Use 'run-all' or 'run-test <filename>'!"
    exit 1
    ;;
esac
