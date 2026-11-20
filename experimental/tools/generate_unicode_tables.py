import re
import sys

source = open(sys.argv[1]).read()

def read_array(name):
    match = re.search(r'let ' + name + r' = \[\|(.*?)\|\]', source, re.S)
    body = match.group(1)
    return [item.strip() for item in body.split(';') if item.strip()]

def read_integers(name):
    return [int(item, 0) for item in read_array(name)]

def emit_ranges(name, values):
    lines = ['internal let %s: Array[UInt32, %d] = [' % (name, len(values))]
    for start in range(0, len(values), 12):
        lines.append('  ' + ', '.join(str(value) for value in values[start:start + 12]) + ',')
    lines.append(']')
    return '\n'.join(lines)

parts = []
for name in ['xid_start', 'xid_continue', 'forbidden', 'bidi_control', 'control']:
    parts.append(emit_ranges(name + '_ranges', read_integers(name)))

keys = read_integers('forbidden_name_keys')
values = [eval(item) for item in read_array('forbidden_name_values')]
lines = ['internal fn find_forbidden_name(code: UInt32) -> Option[StringSlice] {', '  match code {']
for key, value in zip(keys, values):
    lines.append('    %d => Some("%s")' % (key, value))
lines.append('    _ => None')
lines.append('  }')
lines.append('}')
parts.append('\n'.join(lines))
print('\n\n'.join(parts))
