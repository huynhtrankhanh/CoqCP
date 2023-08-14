import { CoqCPAST } from './parse'

const indent = '    '

export const cppCodegen = ({ environment, procedures }: CoqCPAST): string => {
  const environmentCode = (() => {
    if (environment === null) return ''
    return (
      'namespace environment {\n' +
      [...environment.arrays].map(([name, description]) => {
        const { itemTypes, length } = description
        return (
          indent +
          'std::tuple<' +
          itemTypes.map((x) => 'u' + x + '_t').join(', ') +
          '> ' +
          name +
          '[' +
          length +
          ']'
        )
      }) +
      '}\n'
    )
  })()

  return '#include <iostream>\n#include <tuple>\n'+environmentCode
}
