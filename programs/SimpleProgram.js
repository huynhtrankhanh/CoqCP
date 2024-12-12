environment({ buffer: array([int8], 20) })
procedure('main', {}, () => {
  range('The number is ', x => { writeChar(x) });
  call(PrintInt64, { buffer: 'buffer' }, 'signed', { num: 1 + 1 })
})
