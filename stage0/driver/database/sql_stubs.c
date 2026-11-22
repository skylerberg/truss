#define CAML_NAME_SPACE
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/mlvalues.h>

#include <sqlite3.h>
#include <string.h>

CAMLprim value truss_take_statement_steps(value statement_value, value sql_value) {
  void *wrapper = *(void **)Data_custom_val(statement_value);
  sqlite3_stmt *statement = wrapper == NULL ? NULL : *(sqlite3_stmt **)wrapper;
  const char *sql = statement == NULL ? NULL : sqlite3_sql(statement);
  if (sql == NULL || strcmp(sql, String_val(sql_value)) != 0) {
    caml_failwith(
        "The sqlite3 binding does not hold a statement first in its wrapper, so "
        "its steps cannot be read.");
  }
  return Val_long(sqlite3_stmt_status(statement, SQLITE_STMTSTATUS_VM_STEP, 1));
}
