COMPILE_EXTREC="./build/mi-tmp compile --test --experimental-records"

TEST_LOCATION="test/extrec/"
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

case $1 in 
  run-test)
    run_test "$2"
    ;;
  run-all)
    run_all
esac