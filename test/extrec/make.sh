COMPILE_EXTREC="./build/mi-tmp compile --test --experimental-records"

TEST_LOCATION="test/extrec/"
OUTPUT_LOCATION="test/extrec/out"

run_test() {
  input_file=$1
  file_prefix=${input_file%.*}
  set +e

  echo "--- $input_file ---"
  $COMPILE_EXTREC --output $OUTPUT_LOCATION/$file_prefix $TEST_LOCATION$input_file > /dev/null
  if [ $? -eq 0 ] 
  then
    echo "Compilation successful!"
    ./$OUTPUT_LOCATION/$file_prefix
    if [ $? -eq 0 ] 
    then 
      echo "Test Successful"
    else 
      echo "Test Failed!"
    fi
    rm ./$OUTPUT_LOCATION/$file_prefix
  else
    echo "Compilation Error!"
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
